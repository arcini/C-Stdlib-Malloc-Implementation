# C-Stdlib-Malloc-Implementation
*NOT INTENDED TO BE COMPILED AND RAN, DRIVER CODE NOT OWNED BY I, ARCINI*

This is a custom implmentation of the standard C library functions malloc(), realloc(), and free(). This implementation uses a segregated free list to keep track of free blocks, and includes segmenting free blocks upon allocation along with free block coalescing upon freeing. 


# Checkpoint 1 Work

Patrick: Implemented the heap checker and contributed to static inline functions

Alex (arcini): Implemented functionality for all other functions used in malloc, realloc, and free including these functions themselves

# Final Submission Work

Alex (arcini): Added free block segmentation when free block gets allocated to a block of much smaller size, Added Coalescing, Moved seglist array to heap area, tons of debugging, fixed static inline functions, fixed heap checker, some absraction of common tasks used in malloc and free

Patrick: some work on heap checker
