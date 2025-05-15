#set text(font: ("Libertinus Serif", "Noto Serif CJK SC"))
#let lb = $bracket.l.double$
#let rb = $bracket.r.double$

= Homework 3.11

1.
令$s_i$表示$x=i$的程序状态（$i in ZZ$），则：
$
  lb c rb={(s_i,s_0)|i in NN}union{(s_i,s_i)|i <0}.
$

2.\
(a)
$
lb"while"space(e)space"do"space{c}rb={(s_i,s_0)|i in NN}union{(s_i,s_i)|i <0}.
$
(b)\
// 记$A_j:={(s_i,s_j)|i<0},space B:={A_j|j in ZZ},space Y:={(s_i,s_0)|i in NN_+}$。则：
// $
//   {X|F(X)=X}={X|X=Y union (union.sq.big Z),Z in P(B)}. 
// $
根据语句本身可以得知，从任意一种程序状态开始执行该语句都会在某一状态终止，因此$F(X)$的不动点是唯一的。
$
  F(X)=X <==> X={(s_i,s_0)|i in NN}union{(s_i,s_i)|i <0}.
$

3.\
错误。容易验证整数相等关系的自反性、传递性和反对称性，因此$(NN,=)$是偏序集。对于$NN$中的任意非空链$S$，满足$a,b in S$当且仅当$a=b$，因此$S={a}$，可知$"lub"(S)=a$。但是该集合不存在最小元，因此对于空链$emptyset$，不存在上确界。所以$(NN,=)$不是完备偏序集。

4.\
错误。记$E_i:=NN_(<=i),space S:={E_i|i in NN}$，易知$S$是$A$中的一条链。如果$"lub"(S)$存在，需要满足$A in.rev"lub"(S)supset.eq union.big_(i in NN)E_i$。又因为$|"lub"(S)|>=|union.big_(i in NN)E_i|=aleph_0$是可数无穷集，因此$A$中不存在$"lub"(S)$，$(A,subset.eq)$不是完备偏序集。

5.\
当$m=n=0$时，结论平凡成立。只需证明$m,n>0$时的情况。\
$
  forall a, b in NN space s.t.space a|b,space exists c in NN space s.t.space b=a c.\
  therefore gcd(b,m)=gcd(a c,m)=gcd(a,m) times gcd((a c)/gcd(a,m),m/gcd(a,m)).\
  therefore gcd(a,m)|gcd(b,m).
$
综上：得证。

6.\
当$m n=0$时，结论平凡成立。只需证明$m,n>0$时的情况。\
$
  forall a, b in NN space s.t.space a|b,space exists c in NN space s.t.space b=a c.\
  therefore lcm(b,m)=(b m)/gcd(b,m)=(a c m)/(gcd(a,m) times gcd((a c)/gcd(a,m),m/gcd(a,m)))=lcm(a,m) times c/(gcd((a c)/gcd(a,m),m/gcd(a,m))).\
  because gcd(a,m)|a ,space gcd(a,m)|m.\
  therefore exists x,y in NN space s.t. space x=a/gcd(a,m),space y=m/gcd(a,m).\
  therefore gcd((a c)/gcd(a,m),m/gcd(a,m))=gcd(x c,y)|c.\
  therefore exists z in NN space s.t. space z=c/(gcd((a c)/gcd(a,m),m/gcd(a,m))).\
  therefore lcm(b,m)=lcm(a,m) times z.\
  therefore lcm(a,m)|lcm(b,m).
$
综上：得证。

7.\
#let leA = $attach(<=, br: A)$
- $leA$的自反性、传递性和反对称性显然成立，$(A,leA)$是偏序集。对于$A$中的任意非空链$S$，若$S$中的元素有限，显然$S$中的最大元素就是它的上确界；若$S$中的元素可数无穷且$omega+1in.not S$，那么$"lub"(S)=omega$，否则$"lub"(S)=omega+1$。因此$"lub"(S)$必定存在，$(A,leA)$是完备偏序集。\ \
- $"succ"$的单调性显然成立。对于连续性给出反例：令$S=NN$，则$"lub"(S)=omega,space "succ"("lub"(S))=omega+1$。$"succ"(S)=NN_+,"lub"("succ"(S))=omega$。因此：$"succ"("lub"(S))=omega+1!="lub"("succ"(S))=omega$。\ \
- 由定义可知$bot=0$。
$
  therefore"lub"(bot,"succ"(bot),"succ"("succ"(bot)),...)="lub"(0,1,2,...)="lub"(NN)=omega!="succ"(omega)=omega+1.
$
得证。