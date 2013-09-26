/*
Made By : Ayush Jain
        : 1101CS09
*/

#include<stdio.h>
#include<stdlib.h>
typedef struct minterm
{
      int minterm,dontcare,checked;
      struct minterm *next;
} Minterm;
struct term
{
      int ones,twos,bits,used;
      Minterm *minterm;
      struct term *next;
};
typedef struct term Implicant;
int nov;
int toBinary(int dec)
{ 
      int rem,c=0,d=1; 
      while(dec!=0)
      {
           rem=dec%2;
           c=rem*d+c;
    	   dec=dec/2;
           d=d*10;
      }
      return c;
}
int countOnes(int bits)
{
      int c=0;
      while(bits!=0)
      {
           if(bits%10==1)
                 c++;
    	   bits=bits/10;
      }
      return c;
}
int posOfTwosEqual(int a,int b)
{
      int r1,r2,c=1; 
      while(a!=0||b!=0)
      {
           r1=a%10;
           r2=b%10;
           if((r1==2||r2==2)&&r1!=r2)
           {
                 c--;
                 break;
           }
    	   a=a/10;
           b=b/10;
      }
      return c;
}
int isPowerOfTwo(int n)
{
      int rem,c=0,p=0; 
      while(n!=0)
      {
           rem=n%10;
           if(rem!=1&&rem!=0)
           {
                 c=0;
                 break;
           }
           if(rem==1)
           {
                 c++;
           }
    	   n=n/10;
    	   p++;
      }
      if(c==1)
            return p;
      else
            return -1;
}
void calculateNoOfVariables(Implicant *h)
{
      int a=-1,i=0;
      while(h!=NULL)
      {
            if(h->minterm->minterm>a)
                  a=h->minterm->minterm;
            h=h->next;
      }
      while(a!=0)
      {
            a=a/2;i++;
      }
      nov=i;
}
Implicant* newImplicant(int bits,int ones,int twos,Minterm *minterm,int used)
{
      Implicant *t=malloc(sizeof(Implicant));
      t->minterm=minterm;
      t->bits=bits;
      t->ones=ones;
      t->twos=twos;
      t->used=used;
      t->next=NULL;
      return t;
}
Implicant* add(Implicant *head,Implicant *t)
{
      Implicant *tail=head,*prev;
      while(1)
      {
            if(t->twos>tail->twos)
            {
                  if(tail==head)
                  {
                        t->next=head;
                        head=t;
                  }
                  else
                  {
                        t->next=tail;
                        prev->next=t;
                  }
                  return head;
            }
            if(tail->bits==t->bits)
                  return head;
            if(tail->next==NULL)
                  break;
            prev=tail;
            tail=tail->next;
      }
      tail->next=t;
      return head;
}
void deleteImplicants(Implicant *h)
{
      Implicant *t=h;
      while(t!=NULL)
      {
            Implicant *temp=t;
            t=t->next;
            free(temp);
      }
}
int i=1;
/*void printt(Implicant *head)
{     
      Implicant *t=head;
      printf("\nMinterms : \n\n");
      while(t!=NULL)
      {
            Minterm *m=t->minterm;
            while(m!=NULL)
            {
                  printf("%d,",m->minterm);
                  m=m->next;
            }
            printf("\t\t\t%d\t\t%d\t\t%d\n",t->bits,t->ones,t->twos);
            t=t->next;
      }
}*/
void print(Implicant *head)
{     
      Implicant *t=head;
      printf("\nExpression %d : ",i++);
      while(t!=NULL)
      {
            if(t->used==2)
            {
                  int m=t->bits,l=1,p=nov;
                  char ch[nov*2+1],ch2[nov*2+1];ch[0]='\0';
                  while(p>0)
                  {
                        if(m%10==2)
                        {p--;m=m/10;continue;}
                        if(m%10==0)
                              ch[l++]='\'';
                        ch[l++]=(char)(64+p--);
                        m=m/10;
                  }
                  l--;p=0;
                  while(ch[l]!='\0')
                        ch2[p++]=ch[l--];
                  ch2[p]='\0';
                  if(ch2[0]=='\0')
                        printf(" 1 ");
                  else
                        printf(" %s ",ch2);
                  printf("+");
            }
            t=t->next;
      }
      printf("\b ");
}
Minterm* mergeMinterms(Minterm *m1,Minterm *m2)
{
      Minterm *m=m1,*head=NULL,*t;int i;
      for(i=0;i<2;i++)
      {
            if(i==1)
                  m=m2;
            while(m!=NULL)
            {
                  if(head==NULL)
                  {      
                        head=malloc(sizeof(Minterm));
                        *head=*m;t=head;head->next=NULL;
                  }
                  else
                  {       
                        t->next=malloc(sizeof(Minterm));
                        *((*t).next)=*m;
                        t=t->next;t->next=NULL;
                  }
                  m=m->next;
            }
      }
      t->next=NULL;
      return head;
}
Implicant* checkAndSetOneBitChange(Implicant *a,Implicant *b)
{
      int s=(a->bits)-(b->bits),neg=0;
      if(s<0)
      {
            s=-s;
            neg++;
      }
      int pos=isPowerOfTwo(s);
      if(pos!=-1)
      {
            Implicant* temp;
            if(neg==0)
                  temp=a;
            else
                  temp=b;
            Implicant* n=newImplicant(temp->bits+s,temp->ones-1,temp->twos+1,mergeMinterms(a->minterm,b->minterm),0);
            return n;
      }
      else
            return NULL;
}
Implicant* generatePrimeImplicants(Implicant* h)
{
      Implicant *t1=h,*head=NULL;
      int unused=0,cunused=0;
      while(t1!=NULL)
      {
            cunused++;
            Implicant *t2=t1->next;
            while(t2!=NULL)
            {
                  if((t1->twos==t2->twos)&&(t1->ones-t2->ones==1||t1->ones-t2->ones==-1)&&posOfTwosEqual(t1->bits,t2->bits)==1)
                  {
                        Implicant *t=checkAndSetOneBitChange(t1,t2);
                        if(t!=NULL)
                        {
                              if(head==NULL)
                              {
                                    head=t;
                                    head->next=NULL;
                              }
                              else
                                    head=add(head,t);
                              t1->used=1;t2->used=1;
                        }
                  }
    	          t2=t2->next;
            }
            if(t1->used==0)
            {
                  unused++;
                  Implicant *b=newImplicant(t1->bits,t1->ones,t1->twos,t1->minterm,0);
                  if(head==NULL)
                  {
                        head=b;
                        head->next=NULL;
                  }
                  else
                        head=add(head,b);
            }
       	    t1=t1->next;
      }
      //printt(head);
      if(unused==cunused)
            return h;
      else
      {
            deleteImplicants(h);
            return generatePrimeImplicants(head);
      }
}
Implicant* takeInput(Implicant *head,int dontcare)
{
      int data=-1;char ch;
      do
      {
    	    ch=getchar();
            if((ch==' '||ch=='\n')&&data!=-1)
            {
                  Minterm *m=malloc(sizeof(Minterm));
		          m->minterm=data;
		          m->dontcare=dontcare;
		          m->next=NULL;
		          m->checked=0;
		          Implicant *t=newImplicant(toBinary(data),countOnes(toBinary(data)),0,m,0);
                  if(head==NULL)
                  {
                       head=t;
                       head->next=NULL;
                  }
          		  head=add(head,t);
                  data=-1;
            }
    	    else if(ch>=48&&ch<=57)
    	    {
                  if(data==-1)
                        data=0;
        		  data=data*10+((int)ch-48);
    	    }
      }while(ch!='\n');
      return head;
}
void removeSubsets(Implicant *h,Minterm *min)
{
      Implicant *t=h,*temp;
      while(t!=NULL)
      {
            if(t->used==1||t->used==2)
            {t=t->next;continue;}
            Implicant *s=h;
            while(s!=NULL)
            {
                  if(s->used==1||s==t)
                  {s=s->next;continue;}
                  Minterm *m=t->minterm;int i=0,j=0,b=0;
                  while(m!=NULL)
                  {
                        if(m->dontcare==1)
                        {m=m->next;continue;}
                        Minterm *p=min;int a=0;
                        while(p!=NULL)
                        {
                              if(m->minterm==p->minterm&&p->checked==1)
                              {a=1;break;}
                              p=p->next;
                        }
                        if(a==1)
                        {m=m->next;continue;}
                        Minterm *n=s->minterm;i++;
                        while(n!=NULL)
                        {
                              if(n->dontcare==1)
                              {n=n->next;continue;}
                              Minterm *p2=min;int c=0;
                              while(p2!=NULL)
                              {
                                    if(n->minterm==p2->minterm&&p2->checked==1)
                                    {c=1;break;}
                                    p2=p2->next;
                              }
                              if(c==1)
                              {n=n->next;continue;}
                              b++;
                              if(m->minterm==n->minterm)
                                    j++;
                              n=n->next;
                        }
                        m=m->next;
                  }
                  if((i==j&&i<b)||i==0)
                        t->used=1;
                  s=s->next;
            }
            t=t->next;
      }
      
}
int checkMinterms(Minterm *m,Implicant *h)
{
      Minterm *min=m;Implicant *temp;int f=0;
      while(min!=NULL)
      {
            if(min->checked==1)
            {min=min->next;continue;}
            Implicant *t=h;int i=0;
            while(t!=NULL)
            {
                  if(t->used==1)
                  {t=t->next;continue;}
                  Minterm *x=t->minterm;
                  while(x!=NULL)
                  {
                        if(x->dontcare==1)
                        {x=x->next;continue;}
                        if(min->minterm==x->minterm)
                        {
                              i++;
                              temp=t;
                        }
                        x=x->next;
                  }
                  t=t->next;
            }
            if(i==1)
            {
                  f=1;temp->used=2;Minterm *z=temp->minterm;
                  while(z!=NULL)
                  {
                        if(z->dontcare==1)
                        {z=z->next;continue;}
                        Minterm *y=m;
                        while(y!=NULL)
                        {
                              if(y->minterm==z->minterm)
                                    y->checked=1;
                              y=y->next;
                        }
                        z=z->next;
                  }
            }
            min=min->next;
      }
      return f;
}
Implicant* copyList(Implicant *c)
{
      Implicant *t=NULL,*head=NULL;
      while(c!=NULL)
      {
            if(head==NULL)
            {
                  head=malloc(sizeof(Implicant));
                  *head=*c;head->next=NULL;t=head;
            }
            else
            {
                  t->next=malloc(sizeof(Implicant));
                  *((*t).next)=*c;t=t->next;t->next=NULL;
            }
            c=c->next;
      }
      return head;
}
void generateEssentialPrimeImplicants(Minterm *min,Implicant *h)
{
      int i=1;
      while(i)
      {
            removeSubsets(h,min);
            i=checkMinterms(min,h);
      }
      
      Implicant *t=h,*r=NULL;int minterm=0;int n=0;int k=0;            //Checking Dominating terms
      Minterm *l=min;int a=0;
      while(t!=NULL)
      {
            if(t->used==1||t->used==2)
            {
                  t=t->next;continue;
            }
            Minterm *m=t->minterm;a=0;
            while(m!=NULL)
            {
                  a++;
                  m=m->next;
            }
            if(a>minterm)
            {
                  minterm=a;n=1;r=NULL;
                  r=copyList(h);
                  l=mergeMinterms(min,NULL);
                  k=1;
            }
            else if(a==minterm)
            {
                  n++;k=1;
                  r=realloc(r,n*sizeof(Implicant));
                  *(r+n-1)=*copyList(h);
                  l=realloc(l,n*sizeof(Minterm));
                  *(l+n-1)=*mergeMinterms(min,NULL);
            }
            if(k==1)
            {
                  k=0;
                  Implicant *d=(r+n-1);
                  while(d!=NULL)
                  {
                        if(d->bits==t->bits)
                        {
                              d->used=2;
                              Minterm *p=d->minterm;
                              while(p!=NULL)
                              {
                                    if(p->dontcare==1)
                                    {p=p->next;continue;}
                                    Minterm *q=(l+n-1);
                                    while(q!=NULL)
                                    {
                                          if(p->minterm==q->minterm)
                                                q->checked=1;
                                          q=q->next;
                                    }
                                    p=p->next;
                              }
                        }
                        d=d->next;
                  }
            }
            t=t->next;
      }      
      
      if(r==NULL)
      {
            print(h);
            return;
      }
      while(n>0)
      {
            generateEssentialPrimeImplicants((l+n-1),(r+n-1));
            n--;
      }
}
Minterm* generateList(Implicant *h)
{
      Minterm *m=NULL;
      while(h!=NULL)
      {
            Minterm *n=h->minterm;
            while(n!=NULL)
            {
                  if(n->dontcare==1)
                  {
                        n=n->next;
                        continue;
                  }
                  if(m==NULL)
                  {
                        m=malloc(sizeof(Minterm));
                        *m=*n;m->next=NULL;
                  }
                  else
                  {
                        Minterm *tail=m;int k=0;
                        while(1)
                        {
                              if(tail->minterm==n->minterm)
                              {
                                    k=1;
                                    break;
                              }
                              if(tail->next==NULL)
                                    break;
                              tail=tail->next;
                        }
                        if(k==1)
                        {
                              n=n->next;
                              continue;
                        }
                        tail->next=malloc(sizeof(Minterm));
                        *((*tail).next)=*n;
                        tail=tail->next;tail->next=NULL;
                  }
                  n=n->next;
            }
            h=h->next;
      }
      return m;
}
main()
{
      system("clear");
      printf("-------------------------------------------------------------------------------\n");
      printf("| ***Welcome to QUINE-MCCLUSKEY METHOD for simplifying boolean expressions*** |\n");
      printf("-------------------------------------------------------------------------------\n");
      printf("\nPlease enter the minterms: ");
      Implicant *head=takeInput(NULL,0);
      printf("\nAny don't care terms (y/n): ");
      char ch,ch2;scanf("%c%c",&ch,&ch2);
      if(ch=='y')
      {
            printf("\nEnter the don't care terms: ");
            head=takeInput(head,1);
      }
      //printt(head);
      calculateNoOfVariables(head);
      head=generatePrimeImplicants(head);
      printf("\n\nThe minimized expression using Quine McCluskey Method is:\n\n");
      generateEssentialPrimeImplicants(generateList(head),head);
      printf("\n\n-------------------------------------------------------------------------------\n\n");
      getch();
}
