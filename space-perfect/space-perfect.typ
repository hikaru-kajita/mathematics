#set heading(numbering: "1.")

#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let lemma = thmbox("lemma", "補題", padding: (top: 0em, bottom: 0em))
#let definition = thmbox("definition", "定義", padding: (top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "系", padding: (top: 0em, bottom: 0em))
#let proof = thmproof("proof", "Proof")

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set page(margin: (x: 30pt))

#set text(
  font: ("New Computer Modern", "Harano Aji Mincho"),
  lang: "ja"
)
#show math.equation: set text(
  font: ("New Computer Modern Math", "Harano Aji Mincho")
)
#show heading: it => it + v(10pt)

#let smallspace = [#h(4pt)];
#let even = [even];
#let odd = [odd];
#let prime = [prime];
#let rad = [rad];

#let indentbox(body) = {
  set par(first-line-indent: 2em, hanging-indent: 2em,);
  text[#body]
}

#align(center)[
  #text(size: 18pt)[宇宙完全数の決定問題について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

= はじめに

$k=2^epsilon q smallspace (q=2^(epsilon+1)-1:prime)$ を偶数完全数とする.

飯高先生によって考案された完全数の平行移動 $sigma(alpha)=2alpha+m$ のうち, $m=2k$ の場合は特に $n=k p smallspace (p:prime, gcd(k, p)=1)$ の形のすべての自然数が解になり, したがって解がとても多いという著しい性質がある.

さて, $k=6$ の場合, $sigma(alpha)=2alpha+2k$ の解で, $6$ の倍数であるものは $alpha=6 p smallspace (p:prime, gcd(k, p)=1), 2^e q^f$ の形に書けることは飯高先生によって既に示されていた.

今回の結果は, それを一般の偶数完全数に一般化したものになる.

= 主定理

#theorem[
  $k$ を偶数完全数とし, $k=2^epsilon q smallspace (q=2^(epsilon+1)-1:prime)$ とする.

  $k divides alpha$ を満たす $sigma(alpha)=2alpha+2k$ の解は以下のいずれかを満たす:

  - $alpha=k p smallspace (p:prime, gcd(k, p)=1)$
  - $alpha=2^e q^f$
]

#proof[
  $k divides alpha$ より, $alpha=2^e q^f L smallspace (e>=epsilon, gcd(L, k)=1)$ と書ける. これを $sigma(alpha)=2alpha+2k$ に代入すると

  $display((2^(e+1)-1) dot (q^(f+1)-1)/(q-1) dot sigma(L)=2^(e+1)q^f L+2^(epsilon+1)q)$. 両辺に $q-1$ をかけて

  $(2^(e+1)-1) dot (q^(f+1)-1) dot sigma(L)=2^(e+1)(q^(f+1)-q^f)L+2^(epsilon+1)q(q-1)$.

  ここで $A=2^(e+1)-1, B=q^(f+1)$ とおいて整理すると $display(A(B-1)sigma(L)=(A+1)(B-B/q))L+2^(epsilon+1)q(q-1).$

  左辺にすべてを移行すると $display( A(B-1)sigma(L)-(A+1)(B-B/q)L-2^(epsilon+1)q(q-1)=0)$.

  $sigma(L)="co"sigma(L)+L$ より $display(A(B-1)"co"sigma(L)+(A(B-1)-(A+1)(B-B/q))L-2^(epsilon+1)q(q-1)=0)$.

  さて, $display(A(B-1)-(A+1)(B-B/q)=(cancel(A B)-A)-(cancel(A B)-(A B)/q+B-B/q)=(A B)/q-A-B+B/q)$.

  $display(1/q (A-q)(B-q)=(A B)/q-A-B+q)$ より, $display(A(B-1)-(A+1)(B-B/q)=1/q (A-q)(B-q)+(B/q-q))$.

  これを代入すると $display(A(B-1)"co"sigma(L)+(1/q (A-q)(B-q)+(B/q-q))L-2^(epsilon+1)q(q-1)=0)$.

  また, $display(A-q=2^(e+1)-2^(epsilon+1)>=0\, B=q^(f+1)>0\, B/q-q>=q^2/q-q=0)$ で, $display(1/q (A-q)(B-q)+(B/q-q)>=0).$

  したがって, $A(B-1)"co"sigma(L)-2^(epsilon+1)q(q-1)<=0. quad dots.c smallspace  (*)$

  ここで $L$ が合成数, つまり $"co"sigma(L)>=2$ と仮定しよう. このとき $display(0>=2A(B-1)-2^(epsilon+1)q(q-1))$.

  さらに $2^(epsilon+1)<=2^(e+1)=A+1, q(q-1)=q^2-q<=B-q$ を代入して $display(0>=2A(B-1)-(A+1)(B-q).)$

  右辺を展開すると, $(2A B-2A)-(A B+B-A q-q)=A B-2A-B+(A+1)q$.

  ところが $(A-1)(B-2)=A B-2A-B+2$ より, $display(0>=(A-1)(B-2)+(A+1)q-2)$ を得る.

  しかし $A=2^(e+1)-1>=1, B>=q^2>=3^2$ より $(A-1)(B-2)>=0$, また $(A+1)q-2>=2 dot 3-2>0$.

  したがって右辺が正になってしまい矛盾.

  したがって $"co"sigma(L)=0, 1$ が得られる.

  $"co"sigma(L)=0$ の場合は $L=1$より $alpha=2^e q^f$ と書ける.

  $"co"sigma(L)=1$ の場合は $L:prime$ で, この場合についてもう少し考察する.

  $(*)$ 式に戻って $"co"sigma(L)=1$ を代入すると, $display(A(B-1)-2^(epsilon+1)q(q-1)<=0)$.

  よって $(2^(e+1)-1)(q^(f+1)-1)-2^(epsilon+1)(q^2-q)<=0$ が成り立つ.

  $q^(f+1)-1>q^2-q$ であるから, $2^(e+1)-1<2^(epsilon+1)$ が成り立つ必要があり, $e>=epsilon$ と合わせて $e=epsilon$ を得る.

  すると $2^(e+1)-1=2^(epsilon+1)-1=q$ より $q(q^(f+1)-1)-(q+1)(q^2-q)<=0$.

  両辺を $q$ で割って $q^(f+1)-1-(q+1)(q-1)<=0$, つまり $q^(f+1)-1<=q^2-1$.

  したがって $f=1$ で, $n=2^e q^f L$ に代入すると $n=2^epsilon q L=k L$.
]

#theorem[
  $k$ を偶数完全数とし, $k=2^epsilon q smallspace (q=2^(epsilon+1)-1:prime)$ とする.

  $alpha=2^e q^f$ が $sigma(alpha)=2alpha+2k$ を満たすとすると, $(e, f)=(epsilon, 3), (2epsilon+1, 1)$.
]

#proof[
  $alpha=2^e q^f$ を代入すると $display((2^(e+1)-1)dot (q^(f+1)-1)/(q-1)=2^(e+1)q^f+2^(epsilon+1) q)$.

  右辺は $q$ の倍数であり, $display((q^(f+1)-1)/(q-1)=1+q+...+q^f)$ は $q$ の倍数でない.

  よって, $2^(e+1)-1$ が $q$ の倍数である.

  さて, $q=2^(epsilon+1)-1$ がメルセンヌ素数であることから, $epsilon+1$ は素数である.

  $ZZ\/q ZZ$ における $2$ の位数を $o_2 (q)$ と書くことにすると, $o_2 (q) | epsilon+1$.

  しかし, $q$ は奇素数であるから, $o_2 (q)eq.not 1$ で, したがって $o_2 (q)=epsilon+1$ が成り立つ.

  さて, $2^(e+1) equiv 1 mod q$ であるから, $o_2 (q) | e+1$, したがって $epsilon+1 | e+1$ で, よってある正整数 $m$ を用いて $e+1=m (epsilon+1)$ と書ける.

  これを代入すると $display((2^(m(epsilon+1))-1) dot (q^(f+1)-1)/(q-1)=2^(m(epsilon+1))q^f+2^(epsilon+1) q)$.

  $2^(m(epsilon+1))q^f$ を左辺に移項して整理すると $display(2^(m(epsilon+1))(q^f-1)/(q-1)-(q^(f+1)-1)/(q-1)=2^(epsilon+1) q quad ... (*))$.

  $2^(epsilon+1)=q+1$ より左辺は $display(2^m ((q+1)(q^f-1))/(q-1)-(q^(f+1)-1)/(q-1)=2^m (q^(f+1)+q^f-q-1)/(q-1)-(q^(f+1)-1)/(q-1))$ で, これは $display((2^m-1)(q^(f+1)-1)/(q-1))$ 以上である.

  したがって, $display((2^m-1)(q^(f+1)-1)/(q-1)<=2^(epsilon+1) q)$ である.

  ここで, $f>2$ を仮定すると, $display((q^(f+1)-1)/(q-1)>q^3+q^2)$ より, $display(2^m-1<=2^(epsilon+1) q/(q^3+q^2)=(q+1)/(q^2+q)=1/q)$.

  これを満たす正整数 $m$ は $m=1$ のみである.

  このとき, $e+1=epsilon+1$ より $e=epsilon$.

  式 $(*)$ に $2^(epsilon+1)=q+1$ と $m=1$ を代入すると, $display(((q^f-1)(q+1))/(q-1)-(q^(f+1)-1)/(q-1)=(q+1)q)$.

  左辺は $display((q^f-q)/(q-1))$ に等しいので, $q^f-q=(q+1)q(q-1)=q^3-q$, よって $f=3$.

  以降は $f<=2$ の場合を考える.

  式 $(*)$ に戻る.

  $f=1$ のとき, これを $(*)$ に代入すると $2^(m(epsilon+1))-q-1=2^(epsilon+1) q$.

  $q=2^(epsilon+1)-1$ より, $2^(m(epsilon+1))=2^(epsilon+1) (2^(epsilon+1)-1)+2^(epsilon+1)-1+1=2^(2(epsilon+1))$.

  したがって, $e+1=m(epsilon+1)=2 epsilon+2$, よって $e=2 epsilon+1$.

  $f=2$ のとき, これを $(*)$ に代入すると $2^(m(epsilon+1))(q+1)-(q^2+q+1)=2^(epsilon+1)q$.

  $2^(epsilon+1)=q+1$ から, $2^m (q+1)^2=(q+1)q+q^2+q+1=2 q^2+2q+1$.

  左辺が偶数, 右辺が奇数となり矛盾.
]

以上2つの定理から, 偶数完全数 $k=2^epsilon q smallspace (q=2^(epsilon+1)-1)$ について, $sigma(alpha)=2alpha+2k$ かつ $k | alpha$ を見たす解は

- $alpha=k p smallspace (p:prime, gcd(k, p)=1)$
- $alpha=2^epsilon q^3$
- $alpha=2^(2epsilon+1)q$

のいずれかに分類できることが証明された.

煩雑なだけの計算になるので省略するが, 逆にこれらはすべて $sigma(alpha)=2alpha+2k$ を満たしていることが確認できる.

= 展望

自然な研究の方向性としては, $alpha$ の条件を緩める, つまり $k | alpha$ であった条件をより弱いものに置き換えるということが考えられる.

たとえば $k=6$ のとき $2 | alpha$ かつ $6 cancel(divides) alpha$ を満たす $alpha<=5 dot 10^11$ は, $alpha=2^4 dot 19, 2^8 dot 499, 2^12 dot 8179, 2^16 dot 131059$ のみであることがわかっている.

そこで, 飯高先生によって, $2 | alpha$ を満たす $sigma(alpha)=2 alpha+12$ の解は $6 | alpha$ もしくは $alpha=2^e p$ の形に書けるもののみであるという予想がなされているが, 証明は困難であろう.
