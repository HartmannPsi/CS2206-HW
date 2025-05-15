#set text(font: ("Libertinus Serif", "Noto Serif CJK SC"))
#let lb =$bracket.l.double$
#let rb =$bracket.r.double$

= Homework 3.18

1. 错误。

2. 错误。

3. 正确。

4. 正确。

5. 正确。

6. 成立。$forall (s_1,s_2)$，令$P:=s_1 '==s_1,space Q:=s_2 '==s_2$。根据题意，${P}c_1{Q}<==>{P}c_2{Q}$，等价于$(s_1,s_2) in lb c_1 rb <==> (s_1,s_2) in lb c_2 rb$，可推出$lb c_1 rb=lb c_2 rb$。得证。

7. 不成立。

8. 成立；可以；不能。

9. `{ y <= x * 2}`.

10. `{exists k, s = 0 + 1 + 2 + ... + k && s - k <= m}`.

11. `{x == n && x >= i * i}`.

12. `{exists x', 100 <= x' + y + z && x' <= 0 && x == 0}`.

13. `{exists x', 0 <= x' + y <= 100 && x' * y <= 100 && x == x' + y}`.

14. `{exists y', exists x', x' == m && y' == n && x == x' + n && y == x - y'}`.

15.
- 1. `{s * t == 1000 && t == 10}`.
- 2. `{exists s', s' * t == 1000 && t == 10 && s = s' * t}`.
- 3. C.
16.
- 1. `{x == n + m && x - y == n}`.
- 2. `{exists y', x == n + m && x - y' == n && y = x - y'}`.
- 3. C.
- 4. C.