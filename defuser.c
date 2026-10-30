#include "defuser.h"

#include <inttypes.h>
#include <stdio.h>

#define MAX_FIELDS 8

/*
 * 把values中count个整数写成一行空格分隔的无符号十进制整数，存入out。
 * 成功返回0；count为0、snprintf出错或结果被截断时返回非零。
 */
static int write_answer(char *out,size_t cap,const uint32_t *values,size_t count)
{
    size_t used=0;
    for(size_t i=0;i<count;++i)
    {
        int size=snprintf(out+used,cap-used,"%s%" PRIu32,i?" ":"",values[i]);
        if(size<0||(size_t)size>=cap-used)return 1;
        used+=(size_t)size;
    }
    return count==0;
}

int solve_phase_1(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=1;
    uint32_t h,m,l,a,b,c;

    //提取challenge的不同32位片段
    h=(uint32_t)(challenge>>32);
    m=(uint32_t)(challenge>>16);
    l=(uint32_t)challenge;

    //依次还原三个辅助函数的计算
    a=(h+51806)^l;
    b=(h+m*8)^0x1604;
    c=(b-l)*5+0x92a9;

    values[0]=c^a;
    return write_answer(out,cap,values,count);
}

int solve_phase_2(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=6;
    uint32_t a;

    //第一个整数由challenge的指定位段决定
    values[0]=((challenge>>30)&15)^27;

    //后五项根据前一项及challenge中不同的6位片段递推
    for(int i=1;i<=5;i++)
    {
        a=challenge>>(5+i*5);
        a=(a&0x3f)^i;
        values[i]=a+values[i-1]*4;
    }

    return write_answer(out,cap,values,count);
}

int solve_phase_3(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=2;

    uint32_t selector=challenge&7;
    uint32_t x=(uint32_t)(challenge>>32)^(uint32_t)(challenge>>3);
    values[0]=selector;

    //根据GDB读取的跳转表确定selector与实际函数的对应关系
    switch(selector)
    {
        case 0://p3_case_1
            values[1]=(2*x)^0xacac;
            break;
        case 1://p3_case_0
            values[1]=3*x+0xd61d;
            break;
        case 2://p3_case_4
            values[1]=5*x+0x39896;
            break;
        case 3://p3_case_2
            values[1]=5*x+0x2444b;
            break;
        case 4://p3_case_6
            values[1]=(x^0x3bae)+(x>>1);
            break;
        case 5://p3_case_7
            values[1]=5*x+0x9afe;
            break;
        case 6://p3_case_3
            values[1]=(x^0xba59)+(x>>2);
            break;
        case 7://p3_case_5
            values[1]=(4*x)^0xb530;
            break;
    }

    return write_answer(out,cap,values,count);
}

//Phase 4递归辅助函数
static uint32_t p4_calc(uint32_t target,uint32_t low,uint32_t high,uint32_t key)
{
    //计算二分区间中点，避免直接相加可能导致的溢出
    uint32_t mid=low+((high-low)>>1);

    //递归终止条件
    if(target==mid)
    {
        return (mid+0x78)^key;
    }

    //向左递归，返回后根据当前中点和key更新结果
    if(target<mid)
    {
        uint32_t r=p4_calc(target,low,mid-1,key);
        return ((3*r)^(mid+key))^29;
    }

    //向右递归，返回时使用不同的异或常数
    else
    {
        uint32_t r=p4_calc(target,mid+1,high,key);
        return ((3*r)^(mid+key))^7;
    }
}

int solve_phase_4(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=1;

    //target限定在0～127，初始搜索区间固定为[0,127]
    uint32_t target=(uint32_t)challenge&0x7f;
    uint32_t low=0;
    uint32_t high=127;
    uint32_t key=(uint32_t)(challenge>>32)^(uint32_t)(challenge>>7);

    values[0]=p4_calc(target,low,high,key);
    return write_answer(out,cap,values,count);
}

//Phase 5链表节点：next使用数组下标表示，-1代表NULL
typedef struct
{
    uint32_t value;
    uint32_t extra;
    int next;
} P5Node;

//按照内存地址顺序排列的12个节点，第三个字段为逻辑后继节点编号
static const P5Node p5_nodes[12]={
    {0x30d8,0x929,7},    //节点0
    {0x3ff4,0xb38,4},    //节点1
    {0x459b,0x336,10},   //节点2
    {0xa9ef,0x81c,11},   //节点3
    {0x9e20,0x769,0},    //节点4
    {0x1be9,0x467,-1},   //节点5
    {0x6366,0x6b,5},     //节点6
    {0x2a98,0x234,2},    //节点7
    {0xd198,0x131,9},    //节点8
    {0x6a54,0x650,1},   //节点9
    {0xa5ff,0xa8a,6},   //节点10
    {0x69cd,0x550,8}     //节点11
};

//函数根据challenge的低3位，从8个不同位置开始遍历
static const int p5_heads[8]={3,11,8,9,1,4,0,7};

int solve_phase_5(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=2;

    //index选择起点，steps决定沿next额外前进的次数
    uint32_t index=challenge&7;
    uint32_t steps=(challenge>>3)&3;

    int cur=p5_heads[index];
    const P5Node *node=&p5_nodes[cur];

    //根据challenge计算初始值
    uint32_t result=(uint32_t)(challenge>>6)^(uint32_t)(challenge>>32);
    uint32_t last_extra=0;

    //首先处理起始节点
    result=result^(node->value);
    result=result^0x3711;
    result+=node->extra;
    last_extra=node->extra;

    //按照链表的逻辑连接关系遍历
    for(uint32_t i=0;i<steps;i++)
    {
        cur=node->next;
        node=&p5_nodes[cur];
        result=result^(node->value);
        result+=node->extra;
        last_extra=node->extra;
    }

    //第二个结果是最后访问节点的extra
    values[0]=result;
    values[1]=last_extra;

    return write_answer(out,cap,values,count);
}

//Phase 6根据函数指针表索引选择对应的运算
static uint32_t p6_apply(uint32_t index,uint32_t x)
{
    switch(index)
    {
        case 0://p6_op_3
            return (x>>5)|(x<<27);

        case 1://p6_op_2
        case 5:
        case 7:
            return ((x>>1)^x)+0xdab5;

        case 2://p6_op_4
            return ((x<<3)|(x>>29))^0x981;

        case 3://p6_op_5
            return (x^0x9c42)+2*x;

        case 4://p6_op_0
            return (x+0xf4b2)^(x>>2);

        case 6://p6_op_1
            return (32*x+0xaad7)^(7*x);
    }

    return 0;
}

int solve_phase_6(uint64_t challenge,char *out,size_t cap)
{
    uint32_t values[MAX_FIELDS]={0};
    size_t count=1;

    uint32_t x=(uint32_t)(challenge>>6)^(uint32_t)(challenge>>32);
    uint32_t index1=challenge&7;
    uint32_t index2=(challenge>>3)&7;

    //第一次间接调用
    uint32_t r1=p6_apply(index1,x);

    //第一次返回值异或固定常数后，作为第二次调用的参数
    uint32_t r2=p6_apply(index2,r1^0x5624);

    values[0]=r2+0x1acb;
    return write_answer(out,cap,values,count);
}

//Honor辅助函数：循环左移7位，再执行加法和异或
static uint32_t secret_mix(uint32_t x)
{
    return (((x<<7)|(x>>25))+0x4e64)^0x4595;
}

int solve_secret(uint64_t challenge,uint64_t context,char *out,size_t cap)
{
    //分别折叠challenge和context的高、低32位
    uint32_t A=(uint32_t)(challenge>>32)^(uint32_t)challenge;
    uint32_t B=(uint32_t)(context>>32)^(uint32_t)context;

    uint32_t a=(uint32_t)context&3;

    //根据secret_phase的三次输入比较恢复计算关系
    uint32_t u=A^B;
    uint32_t v=(0x4e64*a)^(uint32_t)(context>>16);
    uint32_t b=secret_mix(u)^v;
    uint32_t c=b^(B+a+0x4595+(A>>7));

    if(cap==0)return 1;

    //前32字节为占位字符，第32～35字节必须为OPEN
    //从第36字节开始输出三个无符号十进制整数
    int n=snprintf(out,cap,
        "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOPEN%" PRIu32 " %" PRIu32 " %" PRIu32,
        a,b,c);

    //检查字符串格式化是否失败或超过缓冲区容量
    if(n<0||(size_t)n>=cap)return 1;

    return 0;
}
