/*
 * mm.c (2017-11405 방승원)
 * 
 * My approach is an implicit allocator, which uses an implicit list to keep track of free blocks.
 * I implemented the next fit approach to find free blocks.
 * 
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Constants from textbook */
#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1<<12) /* default size for expanding the heap */

#define MINBLOCKSIZE        16

/* Macros from textbook */
#define MAX(x, y)           ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))

/* Read/Write a word at address p */
#define GET(p)              (*(size_t *)(p))
#define PUT(p, val)         (*(size_t *)(p) = (val))

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* global variables */
static char *heap_ptr = 0;
static char *last_ptr = 0;

/* new functions */
static void *extend_heap(size_t words);
static void *next_fit(size_t size);
static void *coalesce(void *bp);
static void place(void *bp, size_t asize);
// static int mm_check();

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create initial empty heap */
    if ((heap_ptr = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    
    PUT(heap_ptr, 0);                               /* Alignment Heading */
    PUT(heap_ptr + (1 * WSIZE), PACK(DSIZE, 1));    /* Prologue Header */
    PUT(heap_ptr + (2 * WSIZE), PACK(DSIZE, 1));    /* Prologue Footer */
    PUT(heap_ptr + (3 * WSIZE), PACK(0, 1));        /* Epilogue Footer */
    heap_ptr += (2 * WSIZE);

    /* Extend empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1; 
    }
    last_ptr = heap_ptr;                            /* Set last allocated block ptr to start of heap */  

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t adjusted_size;               /* Adjusted block size */
    size_t extended_size;               /* Amount to extend heap if no fit */
    char *bp;

    if (size == 0)                      /* Check invalid requests */
        return NULL;   
                     
    if (size <= DSIZE)                  /* Adjust block size to inclued overhead and alignment requirements */
        adjusted_size = DSIZE * 2;
    else
        adjusted_size = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search free list for a fit */
    if ((bp = find_fit(adjusted_size)) != NULL) {
        place(bp, adjusted_size);
        last_ptr = bp;
        return bp;
    }   

    /* If not fit found, get more memory and place the block */
    extended_size = MAX(adjusted_size, CHUNKSIZE);
    if ((bp = extend_heap(extended_size / WSIZE)) == NULL)
        return NULL;
    
    place(bp, adjusted_size);
    last_ptr = bp;
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (!ptr)                               /* check if given ptr argument is valid */
        return;
    
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *old_bp = ptr;
    void *new_bp;
    size_t copy_size;

    if (size != NULL) {
        /* Allocate new block */
        if ((new_bp = mm_malloc(size) == NULL)
            return NULL;

        if (old_bp == NULL)
            return new_bp;

        /* Check size of original block */
        copy_size = GET_SIZE(HDRP(old_bp)) - DSIZE;
        if (size < copy_size)
            copy_size = size;

        /* Copy memory from old block to new block, then free the old block */
        memcpy(new_bp, old_bp, copy_size);
    }
    
    mm_free(old_bp);

    return new_bp;
}

/* HELPER FUNCTIONS */

/*
 * extend_heap - extends heap by CHUNKSIZE and creates initial free block
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t adjusted_size;

    /* round up requested size to nearest multiple of 2 words and allocate */
    adjusted_size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(adjusted_size)) == (void*)-1)
        return NULL;
    
    PUT(HDRP(bp), PACK(adjusted_size, 0));  /* Free block header */
    PUT(FTRP(bp), PACK(adjusted_size, 0));  /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    return coalesce(bp);
}

/*
 * coalesce - perform coalesce as given in textbook
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // if (prev_alloc && next_alloc) {                         /* Case 1 */
        last_ptr = bp;
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {                       /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {                       /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                                      /* Case 4 */
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    last_ptr = bp;
    return bp;
}

/*
 * find_fit - find first free block that fits, next fit : search list starting where previous search finished
 */
static void *find_fit(size_t size)
{
    void *bp = last_ptr;                                                        /* point to last searched position */

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {     /* Search from the last searched position */
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size) {
            last_ptr = bp;
            return bp;
        }
    }

    bp = heap_ptr;
    while (bp < last_ptr) {                                                     /* If no space after the last searched position, go back to the front of the heap */
        bp = NEXT_BLKP(bp);
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= size) {
            last_ptr = bp;
            return bp;
        }
    }

    return NULL;
} 

/*
 * place - place requested block at the beginning of free block
 *      split if the size of the remainder is leq than minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    /* Split if size of remainder is larger than or equal to the minimum block size */
    if ((csize - asize) >= 2 * DSIZE) {     /* Split! */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }

    else {                                  /* Cannot split, use full block */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* Heap Consistency Checker */

/*
static int mm_check() {
    void *next;

    // Is every block in the free list marked as free? - Implicit, so no free list
    
    // Are there any contiguous free blocks that somehow escaped coalescing?
    for (next = heap_ptr; GET_ALLOC(HDRP(next)) == 0; next = NEXT_BLKP(next)) {
        char *prev = PREV_BLKP(HDRP(next));
        if ((prev != NULL) && (GET_ALLOC(HDRP(prev))) && (HDRP(next) - FTRP(prev) == DSIZE)) {
            printf("Consistency Error : Block %p missed coalescing", next);
            return 1;
        }
    }

    // Is every free block actually in the free list? - Implicit, so no free list
    // Do the pointers in the free list point to valid free blocks? - Implicit, so no free list

    // Do any allocated blocks overlap?
    for (curr = heap_ptr; (NEXT_BLKP(curr) == NULL) || (GET_SIZE(HDRP(curr)) == 0); curr = NEXT_BLKP(curr)) {
        if (GET_ALLOC(HDRP(curr))) {
            void *next = NEXT_BLKP(curr);
            if (curr + GET_SIZE(HDRP(curr)) - WSIZE >= next) {
                printf("Consistency Error : Block %p overlaps next block space", curr);
                return 1;
            }
        }
    }

    // Do the pointers in a heap block point to valid heap addresses?
    for (next = heap_ptr; NEXT_BLKP(next) != NULL; next = NEXT_BLKP(next)) {
        if (next < mem_heap_lo() || mem_heap_hi()) {
            printf("Consistency Error : Block %p outside designated heap space", next);
            return 1;
        }
    }

    return 0;
}
*/