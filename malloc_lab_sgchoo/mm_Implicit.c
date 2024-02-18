/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
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
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Choo SungKyul",
    /* First member's email address */
    "choosg@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 8의 배수로 padding

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros*/

// 기본 사이즈 상수 정의
#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1 << 12)                   // 4096byte

#define MAX(x, y)           ((x) > (y)) ? (x) : (y)

#define PACK(size, alloc)   ((size) | (alloc))          // or연산자로 사이즈 + 할당 여부 반환

#define GET(p)              (*(unsigned int *)(p))          // get
#define PUT(p, size)        (*(unsigned int *)(p) = size)   // set

#define GET_SIZE(p)         (GET(p) & ~0x7)             // 뒷자리 3개를 제외한 나머지 수 즉, 해당 블록의 사이즈 반환
#define GET_ALLOC(p)        (GET(p) & 0x1)              // 뒷자리 3개만 확인 즉, 해당 블록의 할당 여부 반환

#define HDRP(bp)            ((char *)(bp) - WSIZE)                      // header block
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // footer block

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variable & Function */
static char *heap_listp;        // 항상 prologue block을 가리키는 정적 전역 변수

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));          // Prologue Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));          // Prologue Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));              // Epilogue Header -> 왜 size == 0?
    heap_listp += 2 * WSIZE;                                // Prologue block 다음 블록 위치 지정

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
Epilogue Header의 size를 0으로 만드는 이유
    오버헤드 최소화: Epilogue header를 최소 크기로 유지함으로써 메모리 오버헤드를 최소화. 
    만약 Epilogue header에 크기를 할당한다면, 실제로 메모리에 할당된 공간이 더 커지고, 
    따라서 할당된 블록의 크기보다 실제로 사용 가능한 공간이 더 커지게 된다. 이는 메모리 사용의 효율성을 저하시킬 수 있다.

    간소화(Simplification): Epilogue header의 크기를 0으로 유지함으로써, 프로그램의 가상 힙의 끝을 나타내는 데 필요한 최소한의 정보만 사용.
    이는 구현을 단순화하고, 메모리 할당 및 해제 작업의 효율성을 향상.
*/
/*
Implicit List Init(size: CHUNKSIZE)
---------------------------------------------------------------------------------------------------------------------------
||  Pro  |  logue |        |                                                                         |        | Epilogue ||
||       |        | Header |                       free block                                        | Footer |          ||
||       |        |        |                                                                         |        |          ||
---------------------------------------------------------------------------------------------------------------------------
*/
// 가용 블록들을 통합
static void *coalesce(void *bp)
{
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // 이전, 다음 블록이 가용 블록인지 확인해서 통합
    if(prev_alloc && next_alloc)
    {
        return bp;
    }

    else if(prev_alloc && !next_alloc)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if(!prev_alloc && next_alloc)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

// 새로운 가용 블록으로 힙 확장
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // New Epilogue Header

    return coalesce(bp);                        // 힙 영역 확장시 이전 블록 혹은 prologue블록과 epilogue 블록과 연결이 돼있는지 확인?
}

/*
두 번째 힙 영역이 할당될 때, 기존에 있던 영역과 연결해주기 위해.
*/

static void *first_fit(size_t asize)
{
    char *tempBp = heap_listp;

    while(GET_SIZE(HDRP(tempBp)) > 0)
    {
        if(GET_SIZE(HDRP(tempBp)) >= asize && !GET_ALLOC(HDRP(tempBp)))
            return tempBp;
        tempBp = NEXT_BLKP(tempBp);
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    size_t beforeFreeBlkSize = GET_SIZE(HDRP(bp));

    // PUT(HDRP(bp), PACK(asize, 1));
    // PUT(FTRP(bp), PACK(asize, 1));
    // bp = NEXT_BLKP(bp);
    // PUT(HDRP(bp), PACK(beforeFreeBlkSize - asize, 0));
    // PUT(FTRP(bp), PACK(beforeFreeBlkSize - asize, 0));

    // 만약 16byte 보다 작다면 사용하지 못하니 패딩을 채워준다.
    if((beforeFreeBlkSize - asize) >= (2*DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(beforeFreeBlkSize - asize, 0));
        PUT(FTRP(bp), PACK(beforeFreeBlkSize - asize, 0));
    }
    else
    {
        PUT(HDRP(bp), PACK(beforeFreeBlkSize, 1));
        PUT(FTRP(bp), PACK(beforeFreeBlkSize, 1));
    }
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendSize;
    char *bp;

    if(size == 0)
        return NULL;

    // header, footer가 달리니, 8byte 배수 크기로 맞춰준다.
    if(size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);

    if((bp = first_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    // 할당된 힙 영역에 공간이 없을때
    extendSize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendSize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
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
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}
