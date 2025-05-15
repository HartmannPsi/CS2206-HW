#set text(font: ("Libertinus Serif", "Noto Serif CJK SC"))
#let lb =$bracket.l.double$
#let rb =$bracket.r.double$

= Homework 3.25

符号执行过程：
```
//@ require true
//@ ensure l * l <= n < (l + 1) * (l + 1)
x = n;
//@ [generated] n == x && true
l = 0;
//@ [generated] 0 == l && n == x && true
r = n + 1;
//@ [generated] n + 1 == r && 0 == l && n == x && true

//@ inv l * l <= n < r * r && l + 1 <= r && x == n
while (l + 1 < r) do {
  //@ [generated] l * l <= n < r * r && l + 1 <= r && x == n && l + 1 < r
  mid = (l + r) / 2;
  //@ [generated] mid == (l + r) / 2 && l * l <= n < r * r && l + 1 <= r && x == n && l + 1 < r
  if (x < mid * mid)
  then { 
    r = mid
    //@ [generated] x < mid * mid && r == mid && (exists r', mid == (l + r') / 2 && l * l <= n < r' * r' && l + 1 <= r' && x == n && l + 1 < r')
  }
  else { 
    l = mid 
    //@ [generated] x >= mid * mid && l == mid && (exists l', mid == (l' + r) / 2 && l' * l' <= n < r * r && l' + 1 <= r && x == n && l' + 1 < r)
  }
  //@ [generated] (x < mid * mid && r == mid && (exists r', mid == (l + r') / 2 && l * l <= n < r' * r' && l + 1 <= r' && x == n && l + 1 < r')) || (x >= mid * mid && l == mid && (exists l', mid == (l' + r) / 2 && l' * l' <= n < r * r && l' + 1 <= r && x == n && l' + 1 < r))
  //@ [target] l * l <= n < r * r && l + 1 <= r && x == n
}
//@ [generated] l * l <= n < r * r && l + 1 <= r && x == n && x >= mid * mid
```
生成的验证条件：
```
n + 1 == r && 0 == l && n == x && true |-- l * l <= n < r * r && l + 1 <= r && x == n

(x < mid * mid && r == mid && (exists r', mid == (l + r') / 2 && l * l <= n < r' * r' && l + 1 <= r' && x == n && l + 1 < r')) || (x >= mid * mid && l == mid && (exists l', mid == (l' + r) / 2 && l' * l' <= n < r * r && l' + 1 <= r && x == n && l' + 1 < r)) |-- l * l <= n < r * r && l + 1 <= r && x == n

l * l <= n < r * r && l + 1 <= r && x == n && x >= mid * mid |-- l * l <= n < (l + 1) * (l + 1)
```