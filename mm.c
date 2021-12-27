/*
 * mm.c
 *
 * Name: Alex Cini, Patrick Barron
 *
 * Description: We created our version of malloc using segregated free lists which were sectioned into size classes of powers of 2.
                In this implementation, we take the size passed into malloc and find the correct size class for which it belongs to. Once determined, we search
                the list until we find a free block big enough to allocate, if not found in this class, we keep going up classes until a suitable block is found (next largest class with a block is guaranteed )
                otherwise we have to allocate a new block on the heap big enough to allocate. When we free
                a block, we find the size of the block freed and place it back in the free list for the size class it belongs to. 
                In checkpoint 1, we do not coalesce nor do we fragment large free blocks into an allocated and free block on malloc.
                In the final submission, we do fragment AND coalesce, this will improve utilization greatly. While the number of segregated free lists is chosen kind of randomly, we found 28 to be sufficient.
                One thing to note is our realloc implementation, we have a naive implementation: simply find a new free block to allocate, allocate it, copy the bits over, then free the original pointer 
                this is pretty bad, since it ignores the potential to simply absorb surrounding free blocks from the oldptr block. However, it is sufficent to give good enough throughput overall.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

//define any constants  or functions using static in line functions
static const int WORD_SIZE = 8;
static const int DOUBLE_WORD_SIZE = 16;
static const int INITIAL_HEAP_SIZE = 128; //size of first free chunk in heap in terms of "blocks" (16 bytes each)
#define NUM_SEGREGATED_LISTS 28

//globals
//seglist[0] points to first size 1 free block, seglist[1] points to first size 2-3 free block, and so on in powers of 2. (4-7, 8-15, 16-31, etc)
void ** seglist;

//pack size and allocated bit into word
static inline size_t pack(size_t size, size_t allocated) {
    return ((size | allocated));
}

//read word from address p
static inline size_t get_word(void* p){
    return (*(uint64_t *) (p));
}

//write word at address p
static inline size_t put_word(void* p, size_t value){
    return (*(uint64_t *)(p) = (value));
}

//read size field from address p
static inline size_t get_size(void* p){
    return get_word(p) & ~0xF;
}

//read allocated bit from address p
static inline size_t get_allocated(void* p){
    return get_word(p) & 0x1;
}

//set allocated bit at address p
static inline void set_allocated(void* p, char allocated) {
    *( (uint64_t *) p) &= ~0xF; //zero the allocated bits
    *( (uint64_t *) p) |= allocated; //set the allocated bits with our value
}

//find header of block given block pointer
static inline uint64_t* header_pointer(void* bp){
    return ((uint64_t *)(bp) - WORD_SIZE/8);
}

//find footer of block given block pointer
static inline uint64_t* footer_pointer(void* bp){
    return ((uint64_t *)(bp) + get_size(header_pointer(bp))/8);
}

//find address of next block
static inline uint64_t* next_block_pointer(void* bp){
    return (footer_pointer(bp) + DOUBLE_WORD_SIZE/8);
}

//find address of previous block
static inline uint64_t* previous_block_pointer(void* bp){
    uint64_t* prevptr = ((uint64_t *)(bp) - get_size(((uint64_t *)(bp) - DOUBLE_WORD_SIZE/8))/8)-DOUBLE_WORD_SIZE/8;
    return (void *)prevptr > mem_heap_lo()+NUM_SEGREGATED_LISTS*WORD_SIZE? prevptr : mem_heap_lo() + WORD_SIZE+NUM_SEGREGATED_LISTS*WORD_SIZE;
}

//returns the address of the previous block in the seglist of block p
static inline uint64_t* get_previous_seglist_block(void* p) {
    return (uint64_t *)get_word(p);
}

//returns the address of the next block in the seglist of block p
static inline uint64_t* get_next_seglist_block(void* p) {
    return (uint64_t *)get_word((void *)((uint64_t *)p+WORD_SIZE/8));
}

//sets the address of the previous block in the seglist of block p
static inline void set_previous_seglist_block(void* p, uint64_t prevptr) {
    if(p != NULL) {
        put_word(p, prevptr);
    }
}

//sets the address of the next block in the seglist of block p
static inline void set_next_seglist_block(void* p, uint64_t nextptr) {
    if(p != NULL) {
        put_word((void *)((uint64_t *)p+WORD_SIZE/8), nextptr);
    }
}

//return the index of the seglist with the smallest size category our size will fit in
static int get_block_segregated_index(size_t size) {
    size /= DOUBLE_WORD_SIZE; //put size in terms of # of blocks
    int result = 0;
    while (size >>= 1) result++; //from https://stackoverflow.com/questions/14767308/how-to-compute-log-base-2-using-bitwise-operators

    if(result >= NUM_SEGREGATED_LISTS) {
        result = NUM_SEGREGATED_LISTS-1;
    }

    return result;
}

//remove a node from its linked list, returns true if the node removed was the head, indicating to the caller that the seglist entry needs updating
//input: pointer to block to be removed, and pointer to hold pointer value to set linked list head to if needed
//returns: boolean value indicating the new head of the linked list if needs to be updated
static bool remove_block(void* p, uint64_t **outhead) {
    //mm_checkheap(__LINE__);
    uint64_t *prevptr = get_previous_seglist_block(p);
    uint64_t *nextptr = get_next_seglist_block(p);

    if(prevptr != NULL) {
        //Has node before it, must update previous node's next pointer to point to 
        set_next_seglist_block(prevptr, (uint64_t)nextptr);
        if(nextptr != NULL) { 
            //in the middle of a linked list
            set_previous_seglist_block(nextptr, (uint64_t)prevptr);
        } 
        return false;
    } else { 
        //HEAD OF THE LIST, no need to update a previous block's next pointer
        if(nextptr != NULL) { 
            //HEAD OF THE LIST, with nodes after, need to update next block's prev pointer
            set_previous_seglist_block(nextptr, (uint64_t)prevptr); 
        } 
        //next block points backwards to null, so it needs to be set by caller function to be the head
        *outhead = nextptr;
        return true;
    }
}

static void add_block_to_seglist(void* p, int size_category) {
    void *tempptr = seglist[size_category];
    seglist[size_category] = p;
    set_next_seglist_block(p, (uint64_t)tempptr);
    set_previous_seglist_block(p, 0);
    if(tempptr != NULL) {
        set_previous_seglist_block(tempptr, (uint64_t)p);
    }

}

//attempts to coalesce newly set free block p with neighboring free blocks (if any)
//  returns true on success, false on error
static bool coalesce(void* p) {
    //mm_checkheap(__LINE__);
    //sanity check
    if(get_allocated(header_pointer(p)) != 0) {
        //not free!
        return false;
    }

    size_t prev_block_allocated = get_allocated(header_pointer(previous_block_pointer(p)));
    size_t next_block_allocated = get_allocated(header_pointer(next_block_pointer(p)));
    uint64_t *outhead = NULL;
    //case 1: surrounded by allocated chunks
    if(prev_block_allocated != 0 && next_block_allocated != 0) {
        //only need to put at head of seglist
        //put our new free block at the head of its seglist
        int size_category = get_block_segregated_index(get_size(header_pointer(p)));
        add_block_to_seglist(p, size_category);
        return true;
    } else if(prev_block_allocated == 1 && next_block_allocated == 0) {
        //coalesce with next block
        size_t total_size = get_size(header_pointer(p)) + get_size(header_pointer(next_block_pointer(p))) + DOUBLE_WORD_SIZE; //adds payloads of the two blocks PLUS the size of removing a footer and a header 
        int size_category = get_block_segregated_index(total_size);
        
        //save addr of the block we are coalescing with
        void *block2 = next_block_pointer(p);

        //set size of header of first block and footer of next block to be the new size
        put_word(header_pointer(p), total_size);
        put_word(footer_pointer(p), total_size); //will evaluate to the footer of the next block because we set the size of the header to the new larger size first
        
        //we need to now adjust the linked list here
        //assume that we need to remove the adjacent from its free list and then insert this new big free block into its free list
        if((remove_block(block2, &outhead)) == true) {
            //need to update head
            seglist[get_block_segregated_index(get_size(header_pointer(block2)))] = outhead;
        }
        
        //set the new big free block to point forward to the head of its seglist, and backwards to null
        add_block_to_seglist(p, size_category);
        return true;
    } else if(prev_block_allocated == 0 && next_block_allocated == 1) {
        //coalesce with previous block
        //very similar to the above case
        size_t total_size = get_size(header_pointer(p)) + get_size(header_pointer(previous_block_pointer(p))) + DOUBLE_WORD_SIZE; //adds payloads of the two blocks PLUS the size of removing a footer and a header 
        int size_category = get_block_segregated_index(total_size);
        
        //save addr of the block we are coalescing with
        void *firstblock = previous_block_pointer(p);
        size_t firstblock_original_size = get_size(header_pointer(firstblock));

        //set size of header of first block and footer of next block to be the new size
        put_word(header_pointer(firstblock), total_size);
        put_word(footer_pointer(firstblock), total_size); //will evaluate to the footer of the next block because we set the size of the header to the new larger size first
        
        //we need to now adjust the linked list here
        //assume that we need to remove the adjacent block from its original free list and then insert this new big free block into its free list
        if((remove_block(firstblock, &outhead)) == true) {
            //need to update head
            seglist[get_block_segregated_index(firstblock_original_size)] = outhead;
        }
        
        //put our new free block at the head of its seglist
        add_block_to_seglist(firstblock, size_category);
        return true;
    } else if(prev_block_allocated == 0 && next_block_allocated == 0) {
        //need to coalesce THREE blocks
        size_t total_size = get_size(header_pointer(p)) + get_size(header_pointer(previous_block_pointer(p))) + get_size(header_pointer(next_block_pointer(p))) + DOUBLE_WORD_SIZE * 2; //additional space from 2 sets of headers/footers
        int size_category = get_block_segregated_index(total_size);

        //save address of the beginning block, aka prev block
        void *firstblock = previous_block_pointer(p);
        size_t firstblock_original_size = get_size(header_pointer(firstblock));
        void *lastblock = next_block_pointer(p);

        //set size of header of first block and footer of next block to be the new size
        put_word(header_pointer(firstblock), total_size);
        put_word(footer_pointer(firstblock), total_size); //will evaluate to the footer of the last block because we set the size of the header to the new larger size on the line above

        //we need to now adjust the linked list here
        //assume that we need to remove both adjacent blocks from their free lists and then insert this new big free block into its corresponding free list
        if((remove_block(firstblock, &outhead)) == true) {
            //need to update head
            seglist[get_block_segregated_index(firstblock_original_size)] = outhead;
        }
        if((remove_block(lastblock, &outhead)) == true) {
            //need to update head
            seglist[get_block_segregated_index(get_size(header_pointer(lastblock)))] = outhead;
        }

        //put our new free block at the head of its seglist
        add_block_to_seglist(firstblock, size_category);
        return true;
    } else {
        return false;
    }
}

//Takes a pointer to a free block, partitions by size, and does all the necessary work to 
//  clean and prep the allocated partition
//  also takes the free fragment from the end, if 32 bytes or larger will create the new free block
//  and add to the corresponding seglist, if < 32 bytes there is no space for header/footer/pointers, so 
//  we will leave it as part of the allocated partition (no fragment)
//  returns: false if error
static bool allocate(void* p, size_t size) {
    //mm_checkheap(__LINE__);
    size_t free_size = get_size(header_pointer(p));

    //sanity check
    if(free_size < size) return false;

    if(free_size <= size + WORD_SIZE * 4) {
        //in this case, there is not enough leftover room to fragment off a free block. We will simply allocate the whole block and return its pointer
        //because allocating whole block, all we have to do is set the allocated bit and clear the pointers from the payload :)
        int size_category = get_block_segregated_index(free_size);
        
        set_allocated(header_pointer(p), 1);
        set_allocated(footer_pointer(p), 1);

        //also need to remove the free block from its free list, since it is now allocated.
        uint64_t *outhead = NULL;
        if((remove_block(p, &outhead)) == true) {
            //need to update head
            seglist[size_category] = outhead;
        }
        return true;
    } else {
        //here, there IS space for header/footer/pointers of the leftover portion, so we will partition
        //start with allocating the first part
        put_word(header_pointer(p), pack(size, 1)); //overwrite header
        put_word(footer_pointer(p), pack(size, 1)); //place footer

        //mem_memset(p, 0, DOUBLE_WORD_SIZE); //set the pointers within the allocated payload back to 0
        //now header & footer for free fragment
        void *free_fragment_ptr = next_block_pointer(p);
        size_t free_fragment_size = free_size-size-DOUBLE_WORD_SIZE;
        put_word(header_pointer(free_fragment_ptr), free_fragment_size); //free_size-size is the total leftover blank fragment, we still have to add a new header and footer, so true size is calculated (minimum 16 bytes)
        put_word(footer_pointer(free_fragment_ptr), free_fragment_size);

        //add the free segment to its seglist
        add_block_to_seglist(free_fragment_ptr, get_block_segregated_index(free_fragment_size));

        //NO NEED TO COALESCE, SINCE p WAS PREVIOUSLY FREE AND THUS MUST BE SURROUNDED BY ALLOCATED BLOCKS
        /*
        if(!coalesce(free_fragment_ptr)) {
            return false; //failed to coalesce?? probably some error
        }
        */

        //also need to remove the now allocated free block from its free list, since it is now allocated and relink list
        uint64_t *outhead = NULL;
        if((remove_block(p, &outhead)) == true) {
            //need to update head of the seglist of the original size category for p
            seglist[get_block_segregated_index(free_size)] = outhead;
        }
        return true;
    } 

    return false;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    //Initialize an empty heap
    mem_sbrk(INITIAL_HEAP_SIZE*DOUBLE_WORD_SIZE+DOUBLE_WORD_SIZE*2 + NUM_SEGREGATED_LISTS*WORD_SIZE); //initial chunk of INITIAL_HEAP_SIZE #of 16 byte blocks, add 16 bytes for prologue and 16 bytes for epilogue
    size_t heapstart = (size_t)mem_heap_lo() + NUM_SEGREGATED_LISTS*WORD_SIZE;


    //check if heap was extended correctly
    if(heapstart == (size_t)-1) {
        return false;
    }

    //allocate array in heap area
    seglist = mem_heap_lo();

    //add fake footer and real header to the first 2 blocks of heap
    put_word((void *)heapstart, 1); // size 0, allocated == 1
    put_word((void *)(heapstart+WORD_SIZE), INITIAL_HEAP_SIZE * DOUBLE_WORD_SIZE); // size of initial heap (one big block), because its multiple of 16, allocated bit is free (0)

    //no need to write a pointer to next free block, as there is only one.

    //add real footer and fake header to end
    size_t heapend = (size_t)mem_heap_hi()+1;
    put_word((void *)(heapend - DOUBLE_WORD_SIZE), INITIAL_HEAP_SIZE * DOUBLE_WORD_SIZE);
    put_word((void *)(heapend - WORD_SIZE), 0x1); // size 0, allocated == 1

    //initialize seglist pointers array
    for(int i = 0; i < NUM_SEGREGATED_LISTS; ++i) seglist[i] = NULL; //set all to null pointer

    //add pointer to first free block to the seglist
    add_block_to_seglist((void *)(heapstart + DOUBLE_WORD_SIZE), get_block_segregated_index(INITIAL_HEAP_SIZE * DOUBLE_WORD_SIZE));

    //zero out next and prev pointers for this free block
    mem_memset((void *)(heapstart+DOUBLE_WORD_SIZE), 0, DOUBLE_WORD_SIZE);

    return true;
}

/*
 * malloc: search seglists starting from appropriate size and call our allocate() function if an existing free block is found, 
    otherwise need to extend heap the appropriate length to make a new free block.
 */
void* malloc(size_t size)
{
    mm_checkheap(__LINE__);

    //return null if size is 0
    if(size == 0) {
        return NULL;
    }

    //DEBUGGING PURPOSE:
    //size += 16;

    //adjust block size for alignment
    size_t aligned_size = align(size);

    //search for a free block
    int seglist_category = get_block_segregated_index(aligned_size);
    void *free_block_ptr = NULL;

    //try every seg list
    for(int i = seglist_category; i < NUM_SEGREGATED_LISTS; ++i) {
        if(seglist[i] == NULL) {
            //no free blocks at all in this category, try next highest
            continue;
        } else {
            //need to search entirety of this free list, if no match found we continue to next largest size class
            void *currptr = seglist[i];
            //void *prevptr = currptr;

            do {
                if(get_size(header_pointer(currptr)) < aligned_size) { 
                    //this block too small
                    //prevptr = currptr;
                    currptr = (void *)get_next_seglist_block(currptr);
                } else {
                    //sufficient size found
                    //currptr holds the pointer to the free block needed
                    free_block_ptr = currptr;
                    break;
                }
            } while(currptr != NULL);

            if(free_block_ptr != NULL) {
                //a free block of sufficient size was found in this category
                //allocate() should take care of it from here!
                if (!allocate(free_block_ptr, aligned_size)) {
                    //BIG ISSUE?!
                    fprintf(stderr, "Malloc encountered an issue in allocating a block\n");
                }
                //DEBUGGING
                //printf("malloc return ptr: %p", currptr);
                return currptr;
            }
        }
    }

    if(free_block_ptr == NULL) {
        //No block suitable found at all, need to allocate
        //TODO: allocate new block on heap of appropriate size, return its pointer
        void * heapend = mem_heap_hi()+1;

        mem_sbrk(aligned_size + DOUBLE_WORD_SIZE);
        put_word(header_pointer(heapend), pack(aligned_size, 1)); // set allocated bit to 1
        put_word(footer_pointer(heapend), pack(aligned_size, 1));

        //recreate fake header again
        put_word(header_pointer(mem_heap_hi()+1), 0x1);
        //DEBUGGING
        //printf("malloc return ptr: %p",heapend);
        return heapend;
    }

    return NULL;
}

/*
 * free
 */
void free(void* ptr)
{
    mm_checkheap(__LINE__);
    //find size of block pointed to by ptr
    //size_t size = get_size(header_pointer(ptr));

    //TODO: confirm its actually an allocated block?

    //DEBUGGING
    //ptr -= 16;
    //set block and allocated bits back to 0
    set_allocated(header_pointer(ptr), 0);
    set_allocated(footer_pointer(ptr), 0);
    

    //coalesce here, this will also add the block to its needed seglist.
    if(!coalesce(ptr)) {
        fprintf(stderr, "free encountered issue coalescing block\n");
    }

    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    mm_checkheap(__LINE__);
    //return malloc if ptr is NULL
    if (oldptr == NULL) {
        return malloc(size);
    }

    //return free if size is 0
    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    //change size of block pointed to by ptr to size bytes

    //Naive implementation: simply find a new free block to allocate, allocate it, copy the bits over, then free the original pointer 
    //  this is pretty bad, since it ignores the potential to simply absorb surrounding free blocks from the oldptr block

    void* newptr = malloc(size);
    mem_memcpy(newptr, oldptr, size);

    return newptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo()+NUM_SEGREGATED_LISTS*WORD_SIZE;
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    //every block in free list marked as free? Go through every list and check whether each block is marked as free
    int free_list_counter = 0;
    for (int i = 0; i < NUM_SEGREGATED_LISTS; ++i){

        if (seglist[i] == NULL){
            continue;
        }

        else{
            void *currptr = seglist[i];

            do {
                if (get_allocated(header_pointer(currptr)) != 0 || get_allocated(footer_pointer(currptr)) != 0){
                    printf("Block marked as allocated in free list ( %p )\n", currptr);
                    return false;
                }
                currptr = get_next_seglist_block(currptr);
                free_list_counter++;
            } while (currptr != NULL);
        }
    }
    //check every block in heap for alignment, heap status, and header and footer equal
    void *heap_check_start = mem_heap_lo()+NUM_SEGREGATED_LISTS*WORD_SIZE + DOUBLE_WORD_SIZE;
    int heap_freeblock_counter = 0;
    void *tempptr = heap_check_start;

    //confirm fake footer is still at beginning with size 0 and is allocated
    if (get_size(heap_check_start-16) != 0 || !get_allocated(heap_check_start-16)){
        printf("Fake footer not correctly assigned at beginning of heap\n");
        return false;
    }

    for (; get_size(header_pointer(tempptr)) > 0; tempptr = next_block_pointer(tempptr)){

        //check if block is in heap
        if (!in_heap(tempptr)){
            printf("Block not in heap\n");
            return false;
        }

        //check if block is aligned
        if (!aligned(tempptr)){
            printf("Block not aligned\n");
            return false;
        }

        //header and footer should be equal
        if (get_word(header_pointer(tempptr)) != get_word(footer_pointer(tempptr))){
            printf("Header and footer not equal: %p\n", tempptr);
            return false;
        }

        //check if block is free
        if (get_allocated(header_pointer(tempptr)) == 0){
            heap_freeblock_counter++;
            //check if block is properly linked to next free block
            //there are 3 cases, case 1: middle block in free list, case 2: last block in free list, case 3: first block in free list
            void *next_free_block = get_next_seglist_block(tempptr);
            void *prev_free_block = get_previous_seglist_block(tempptr);

            //case 1: middle block
            if (prev_free_block != NULL){
                if (next_free_block != NULL){
                    if (tempptr != get_previous_seglist_block(next_free_block) || tempptr != get_next_seglist_block(prev_free_block)){
                        printf("Free blocks not linked correctly to middle free block: %p\n", tempptr);
                        return false;
                    }
                }
                else{
                    //case 2: last block
                    if (tempptr != get_next_seglist_block(prev_free_block)){
                        printf("Previous free block not linked correctly to last free block: %p\n", tempptr);
                        return false;
                    }
                }
            }
            else{
                //case 3: first block
                if (next_free_block != NULL && tempptr != get_previous_seglist_block(next_free_block)){
                    printf("Next free block not linked correctly to the previous free block: %p\n", tempptr);
                    return false;
                }
            }
            
        }
        else {
            //make sure allocated blocks are not overlapping
            if (((tempptr > mem_heap_lo()+NUM_SEGREGATED_LISTS*WORD_SIZE + DOUBLE_WORD_SIZE && header_pointer(tempptr) <= footer_pointer(previous_block_pointer(tempptr))) || (footer_pointer(tempptr) >= header_pointer(next_block_pointer(tempptr))))) {
                printf("Allocated blocks are overlapping (%p and %p)\n", tempptr, previous_block_pointer(tempptr));
                return false;
            }
        }

    }

    //number of free blocks in heap should equal number of free blocks in free list
    if (heap_freeblock_counter != free_list_counter){
        printf("Free blocks don't match between heap and free list\n");
        return false;
    }

    //confirm fake header is still at the end, size is 0 and is allocated
    if (get_size(header_pointer(tempptr)) != 0 || !get_allocated(header_pointer(tempptr))){
        printf("Fake header not correctly assigned at end of heap\n");
        return false;
    }


#endif /* DEBUG */
    return true;
}

/*static void print_block(void *p){
    size_t header_size, footer_size, header_allocated, footer_allocated;
    header_size = get_size(header_pointer(p));
    footer_size = get_size(footer_pointer(p));
    header_allocated = get_allocated(header_pointer(p));
    footer_allocated = get_allocated(footer_pointer(p));
    printf("Header size:" )
}*/
