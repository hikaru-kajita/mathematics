#set heading(numbering: "1.")

#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let proposition = thmbox("proposition", "命題", padding: (top: 0em, bottom: 0em))
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
#set math.equation(numbering: "(1)")

#let nonumber = math.equation.with(
  block: true,
  numbering: none,
)

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
  #text(size: 18pt)[部分乗数付きオイラー型メルセンヌ完全数]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

飯高先生は, 一般化されたメルセンヌ素数を解の一部にもつ乗数付きオイラー型メルセンヌ完全数を定義された.

具体的には, $a=p dot 2^e+m+1:prime, A=p dot 2^e$ をもとに定義式が構成されている.

これを変更したものが筆者の考案したオイラーII型メルセンヌ完全数であり, $a=p dot 2^e+m+1:prime, A=2^e$ をもとに定義式が構成されている.

今回はこれらの二つをもとに片方にだけ乗数をつけた完全数を定義した.

以下, $p$ は奇素数であると仮定する.

$a=p dot 2^e, A=2^e+m+1:prime$ とし, これをもとに定義式をつくる.

まず, $phi(A)=2^e+m$ より $p{phi(A)-m}=a$.

また, $2phi(a)=(p-1)2^e=(A-m-1)(p-1)$.

まとめると

$ cases(p{phi(A)-m}=a, 2phi(a)=(A-m-1)(p-1)) $ <def-partialmult>

が得られ, これを部分乗数付きオイラー型メルセンヌ完全数と定義する.

= $m:even$ の場合

#theorem[
  $m:even$ のとき, 部分乗数付きオイラー型メルセンヌ完全数は

  - $a=2^e p^f, A=2^e p^(f-1)+m+1:prime$
  - $M=1-m$ とおいたとき, $M>0$ で, $M-2phi(M)=1, p divides.not M$ を満たし, $a=p M, A=1$.
]

$phi(n) divides n-1$ を満たす合成数 $n$ は存在しないとするのが Lehmer's totient problemで, これが正しければ $M-2phi(M)=1$ に解は存在しない.

が, これは素数の積と和のからむ未解決問題であり, 解の発見/不存在の証明は困難であろう.

#proof[
  $a$ が偶数であることを示したいので, $phi(A):even$, つまり $A=1, 2$ の可能性を先に考える.

  (1) $A=1$ の場合

  定義式に代入すると, $a=p(1-m)$ と $2phi(a)=-m(p-1)$ が得られる.

  したがって, $m<=0$ で, $M=1-m$ とおくと $M>=1$.

  ここで $p | M$ とすると, $p^2 | a$ より $p | 2phi(a)$ となるが, これは $2phi(a)=-m(p-1)=(M-1)(p-1)$ に矛盾.

  したがって $p divides.not M$ で, $phi(a)=phi(p)phi(M)=(p-1)phi(M)$ より, $2phi(a)=2(p-1)phi(M)=(M-1)(p-1)$.

  よって $2phi(M)=M-1$, つまり $M-2phi(M)=1$.

  (2) $A=2$ の場合

  定義式に代入すると, $a=p(1-m), 2phi(a)=(1-m)(p-1)$ が得られる.

  したがって, $display((2phi(a))/a=((1-m)(p-1))/(p(1-m))=(p-1)/p)$.

  $display(phi(a)/a=1/2 dot (p-1)/p)$ が成り立つ.

  この解のひとつに $a=2p$ が挙げられる.

  さて, $display(phi(n)/n=phi(m)/m <==> rad(n)=rad(m))$ を主張する $phi$ 同値定理より, $a=2^e p^f$ の形に書ける.

  しかし, $a=p(1-m)$ より $a:odd$ であることに矛盾するので, $A=2$ の場合解は存在しない.

  (3) $A>2$ の場合

  $phi(A)$ は偶数なので $a=2^e L smallspace (e>0, L:odd)$ と書ける.

  これを定義式に代入すると $2^e L=p{phi(A)-m}, 2^e phi(L)=(A-m-1)(p-1)$ が得られる.

  したがって, $display(phi(L)/L=(2^e phi(L))/(2^e L)=((A-m-1)(p-1))/(p{phi(A)-m}))$.

  さて, $2^e L=p{phi(A)-m}$ より $L$ は $p$ の倍数で, $L=p^f M smallspace (f>0, p divides.not M)$ と書ける.

  このとき, $display(phi(L)/L=(p^(f-1)(p-1)phi(M))/(p^f M)=(p-1)/p dot phi(M)/M)$ より, $display(phi(M)/M=(A-m-1)/(phi(A)-m))$.

  $A>2$ より, $phi(A)<=A-1$ であるから, 上の式は両辺 $1$ に等しく, よって $M=1, A:prime$.

  したがって, $a=2^e L=2^e p^f M=2^e p^f, A:prime, p{phi(A)-m}=a$ より, $A=2^e p^(f-1)+m+1$.
]

= $m:odd$ の場合

#align(center)[
  #let subtable(m: content, a: content) = table(
    columns: 2,
    table.cell(colspan: 2, $m=#m$),
    $a$, $A$,
    $#a$, $2$
  )
  #figure(
    grid(
      columns: 7,
      gutter: 10pt,
      subtable(m: $-1$, a: $2 dot 3$),
      subtable(m: $-3$, a: $2^2 dot 3$),
      subtable(m: $-5$, a: $2 dot 3^2$),
      subtable(m: $-7$, a: $2^3 dot 3$),
      subtable(m: $-11$, a: $2^2 dot 3^2$),
      subtable(m: $-15$, a: $2^4 dot 3$),
      subtable(m: $-17$, a: $2 dot 3^3$),
      subtable(m: $-23$, a: $2^3 dot 3^2$),
      subtable(m: $-31$, a: $2^5 dot 3$),
      subtable(m: $-35$, a: $2^2 dot 3^3$),
      subtable(m: $-47$, a: $2^4 dot 3^2$),
      subtable(m: $-53$, a: $2 dot 3^4$),
      subtable(m: $-63$, a: $2^6 dot 3$),
      subtable(m: $-71$, a: $2^3 dot 3^3$),
    ),
    caption: [$p=3, m:odd, a:even$]
  )
]

#theorem[
  $m:odd$, $a:even$ を満たす部分乗数付きオイラー型メルセンヌ完全数は $m<0, a=2^e p^f=p(1-m), A=2$ に限る.
]

#proof[
  定義式より $p divides a$ なので, $a=p^f M smallspace (p divides.not M, f>0$ とおける.

  これを定義式に代入すると $phi(A)-m=p^(f-1)M, 2p^(f-1)phi(M)=A-m-1$ が得られる.

  また, $M:even=2^e L smallspace (e>0, L:odd)$ と書け, これを代入すると $phi(A)-m=2^e p^(f-1)L, 2^e p^(f-1)phi(L)=A-m-1$ となり, これを引くと $2^e p^(f-1)"co"phi(L)+"co"phi(A)=1$ が得られる.

  (1) $"co"phi(L)=1, "co"phi(A)=0$ の場合 #indentbox[
    $L=q:prime, A=1$.

    これを $phi(A)-m=p^(f-1)M, 2p^(f-1)phi(M)=A-m-1$ に代入すると $1-m=2^e p^(f-1)q, 2^e p^(f-1)(q-1)=-m$.

    2つ目の式において, 左辺が偶数, 右辺が奇数となり矛盾.
  ]

  (2) $"co"phi(L)=0, "co"phi(A)=1$ の場合 #indentbox[
    $L=1, A=q:prime$.

    しかし, 定義式 $p(phi(A)-m)=a$ より, $phi(A):odd$ でなければならない.

    よって $A=2$ で, これを代入すると $p(1-m)=a=2^e p^f$ が得られる.
  ]
]

さて, 一般に $m:odd, a:odd$ の場合についてこの完全数を解くことは難しい.

しかし, 個別の $m$ についてであれば解くことはできる.

いま, $a=p^f M smallspace (p divides.not M)$ を代入すると $phi(A)-m=p^(f-1)M, 2p^(f-1)phi(M)=A-m-1$ が得られる.

さて, 二番目の式から $A:even=2^e L smallspace (e>0,L:odd)$ と書ける.

これをさらに代入して $2^(e-1)phi(L)-m=p^(f-1)M, 2p^(f-1)phi(M)=2^e L-m-1$ となる.

一番目の式を二倍して二番目の式から引くと $-2p^(f-1)"co"phi(M)=2^e"co"phi(L)+m-1$, 整理すると

$ 2^(e-1)"co"phi(L)+p^(f-1)"co"phi(M)=(1-m)/2 $ <base>

これを用いて特定の $p, m$ の場合について, 解を確定させていくことが可能になる.

また, ここから, 一般に $m>1$ のとき $m:odd,a:odd$ を満たす部分乗数付きオイラー型メルセンヌ完全数は存在しないことがわかる.

以下, $p=3$ の場合のいくつかの例について考える.

#theorem[
  $p=3, m=1$ のとき $a:odd$ を満たす部分乗数付きオイラー型メルセンヌ完全数は $(a, A)=(3, 4), (9, 8)$ のみ.
]

#proof[
  @base より, $2^(e-1)"co"phi(L)+p^(f-1)"co"phi(M)=0$.

  よって $"co"phi(L)="co"phi(M)=0$ より $L=M=1$.

  つまり $a=p^f=3^f, A=2^e$ となるが, これを一番目の定義式に代入すると $p{phi(A)-m=a}$ より $3(2^(e-1)-1)=3^f$, したがって $2^(e-1)-1=3^(f-1)$.

  この解が $(e, f)=(2, 1), (3, 2)$ しか存在しないことはよく知られており, このとき $(a, A)$ はそれぞれ $(3, 4), (9, 8)$.

  これらが解になっていることは計算で確かめられる.
]

#align(center)[
  #figure(
    table(
      columns: 2,
      stroke: none,
      table.hline(start: 0),
      table.header(table.vline(start: 0), $a$, table.vline(start: 0), $A$, table.vline(start: 0)),
      table.hline(start: 0),
      $9$, $2 dot 3$,
      table.hline(start: 0),
      $3 dot 5$, $2^3$,
      $3 dot 17$, $2^5$,
      $3 dot 257$, $2^9$,
      $3 dot 65537$, $2^17$,
      table.hline(start: 0),
    ),
    caption: $p=3,m=-1,a:odd$
  )
]

#theorem[
  $p=3, m=-1$ のとき $a:odd$ を満たす部分乗数付きオイラー型メルセンヌ完全数は $(a, A)=(9, 6), (3(2^(e-1)+1),2^e)$. ただし $2^(e-1)+1$ は3以外のフェルマ素数.
]

#proof[
  @base より, $2^(e-1)"co"phi(L)+p^(f-1)"co"phi(M)=1$.

  (1) $2^(e-1)"co"phi(L)=1, p^(f-1)"co"phi(M)=0$ の場合 #indentbox[
    このとき $L=q:prime, M=1, 2^(e-1)=1$.

    したがって $a=3^f, A=2q$.

    二番目の定義式に代入すると $2phi(a)=(A-m-1)(p-1)$ より $2 dot 2 dot 3^(f-1)=2q dot 2$.

    つまり $3^(f-1)=q$ となるから, $q=3^(f-1)=3$ が確定する.

    よって $a=3^2=9, A=2 dot 3=6$.
  ]

  (2) $2^(e-1)"co"phi(L)=0, p^(f-1)"co"phi(M)=1$ の場合 #indentbox[
    このとき $L=1, f=1, M=q:prime$.

    したがって $a=3q, A=2^e$.

    一番目の定義式に代入すると $p{phi(A)-m}=a$ より $3(2^(e-1)+1)=3q$.

    よって $q=2^(e-1)+1$ となり, $q$ はフェルマ素数である.

    なお, $a:even$ や $3 divides.not M$ の制約より $e>2$.
  ]
]

#align(center)[
  #figure(
    grid(
      gutter: 10pt,
      columns: 2,
      table(
        columns: 2,
        stroke: none,
        table.hline(start: 0),
        table.header(
          table.vline(start: 0),
          $a$,
          table.vline(start: 0),
          $A$,
          table.vline(start: 0)
        ),
        table.hline(start: 0),
        $3^4$, $2^2 dot 13$,
        $3^8$, $2^2 dot 1093$,
        $3^14$, $2^2 dot 797161$,
        $3^72$, $2^2 dot (3.75 times 10^33)$,
        $3^104$, $2^2 dot (6.96 times 10^48)$,
        $3^542$, $2^2 dot (6.63 times 10^257)$,
        table.hline(start: 0),
      ),
      table(
        columns: 2,
        stroke: none,
        table.hline(start: 0),
        table.header(
          table.vline(start: 0),
          $a$,
          table.vline(start: 0),
          $A$,
          table.vline(start: 0)
        ),
        table.hline(start: 0),
        $3 dot 5$, $2 dot 3$,
        $3 dot 7$, $2 dot 5$,
        $3 dot 13$, $2 dot 11$,
        $3 dot 19$, $2 dot 17$,
        $3 dot 31$, $2 dot 29$,
        $3 dot 43$, $2 dot 41$,
        table.hline(start: 0)
      )
    ),
    caption: [$p=3, m=-3, a:odd$]
  )
]

#theorem[
  $p=3, m=-3$ のとき $a:odd$ を満たす部分乗数付きオイラー型メルセンヌ完全数は $(a, A)=(3^f, 4q), (3r, 2s)$ と書ける.

  ただし, $display(q=(3^(f-1)-1)/2)$ は素数で, $r, s$ は $r=s+2$ を満たす双子素数.
]

#proof[
  @base から, $2^(e-1)"co"phi(L)+p^(f-1)"co"phi(M)=2$.

  (1) $2^(e-1)"co"phi(L)=2, p^(f-1)"co"phi(M)=0$ の場合 #indentbox[
    $M=1$ が成り立ち, $(2^(e-1), "co"phi(L))=(1, 2), (2, 1)$ のいずれかになる.

    しかし, $"co"phi(L)=2$ の唯一の解は $L=4$ なので, これは $L:odd$ に矛盾.

    したがって $2^(e-1)=2, "co"phi(L)=1$ より $L=q:prime, 2^e=4$.

    つまり $a=3^f, A=4q$ となり, これを一番目の定義式に代入すると $p{phi(A)-m}=a$ より $3(2q-2+3)=3^f$, よって $display(q=(3^(f-1)-1)/2)$ が得られる.
  ]

  (2) $2^(e-1)"co"phi(L)=1, p^(f-1)"co"phi(M)=1$ の場合 #indentbox[
    $2^e=2, L=s:prime, p^f=3, M=r:prime$ がわかる.

    よって $a=3r, A=2s$ となり, 一番目の定義式に代入すると $p{phi(A)-m}=a$ より $3(s-1+3)=3r$, よって $s+2=r$ がわかる.
  ]

  (3) $2^(e-1)"co"phi(L)=0, p^(f-1)"co"phi(M)=2$ の場合 #indentbox[
    $L=1, p^f=3, M=4$ がわかる.

    しかし, $M=4$ とすると $a:odd$ を満たさなくなってしまう.
  ]
]

#align(center)[
  #figure(
    grid(
      gutter: 10pt,
      columns: 2,
      table(
        columns: 2,
        stroke: none,
        table.hline(start: 0),
        table.header(
          table.vline(start: 0),
          $a$,
          table.vline(start: 0),
          $A$,
          table.vline(start: 0)
        ),
        table.hline(start: 0),
        $3 dot 13$, $2^2 dot 5$,
        $3 dot 17$, $2^2 dot 7$,
        $3 dot 29$, $2^2 dot 13$,
        $3 dot 37$, $2^2 dot 17$,
        $3 dot 41$, $2^2 dot 19$,
        $3 dot 61$, $2^2 dot 29$,
        table.hline(start: 0),
      ),
      table(
        columns: 2,
        stroke: none,
        table.hline(start: 0),
        table.header(
          table.vline(start: 0),
          $a$,
          table.vline(start: 0),
          $A$,
          table.vline(start: 0)
        ),
        table.hline(start: 0),
        $3^2 dot 7$, $2^5$,
        $3^2 dot 23$, $2^7$,
        $3^2 dot 1367$, $2^13$,
        $3^2 dot 87383$, $2^19$,
        $3^2 dot 5592407$, $2^25$,
        $3^2 dot 1466015503703$, $2^43$,
        table.hline(start: 0)
      )
    ),
    caption: [$p=3, m=-5, a:odd$]
  )
]

#theorem[
  $p=3, m=-5$ のとき $a:odd$ を満たす部分乗数付きオイラー型メルセンヌ完全数は $(a,A)=(3q,4r),(9s,2^e)$.

  ただし $q, r, s$ は素数で, $q=2r+3$ と $display(s=(2^(e-1)+5)/3)$ で, $(q, r)eq.not(7, 2), s eq.not 3$.
]

#proof[
  @base から, $2^(e-1)"co"phi(L)+p^(f-1)"co"phi(M)=3$.

  (1) $2^(e-1)"co"phi(L)=3, p^(f-1)"co"phi(M)=0$ の場合 #indentbox[
    $2^e=2, L=9, M=1$ がわかる.

    よって $a=3^f, A=18$ となって, これを一番目の定義式に代入すると $p{phi(A)-m}=a$ より $6+5=3^(f-1)$ となるが, これを満たす $f$ は存在しない.
  ]

  (2) $2^(e-1)"co"phi(L)=2, p^(f-1)"co"phi(M)=1$ の場合 #indentbox[
    $L:odd$ より $2^e=4, L=r:prime, p^f=3, M=q:prime$.

    よって $a=3q, A=4r$ となって, これを一番目の定義式に代入すると $p{phi(A)-m}=a$ より $2r-2+5=q$, よって $q=2r+3$.

    ただ $L:odd$ より $(q, r)=(7, 2)$ だけ除外される.
  ]

  (3) $2^(e-1)"co"phi(L)=1, p^(f-1)"co"phi(M)=2$ の場合 #indentbox[
    $p^(f-1)$ は奇数だが, $"co"phi(M)=2$ の唯一の解 $M=4$ は $a:odd$ を満たさない.
  ]

  (4) $2^(e-1)"co"phi(L)=0, p^(f-1)"co"phi(M)=3$ の場合 #indentbox[
    $"co"phi(M)=3$ を満たすとすると $M=9$ となり, これは $3 divides.not M$ に反する.

    よって $p^f=9, M=s:prime, L=1$ より, $a=9s, A=2^e$.

    これを一番目の定義式に代入すると $p{phi(A)-m}=a$ より $2^(e-1)+5=3s$, つまり $display(s=(2^(e-1)+5)/3)$.

    ただ, $2, 3 divides.not M$ より $s=2, 3$ だけ除外される.
  ]
]

= ダブルB型解

#definition[
  $alpha, beta$ を固定された正整数の定数とする.

  $a=alpha P, A=beta Q smallspace (P, Q:prime, gcd(alpha, P)=gcd(beta, Q)=1)$ の形に書ける部分乗数付きオイラー型メルセンヌ完全数が2個以上存在するとき, その $a, A$ をダブルB型解という.
]

#align(center)[
  #figure(
    grid(
      columns: 3,
      gutter: 10pt,
      table(
        stroke: none,
        columns: 2,
        table.hline(start: 0),
        table.vline(start: 0),
        table.cell(colspan: 2, $m=-3$),
        table.vline(start: 0),
        table.hline(start: 0),
        $a$, table.vline(start: 1), $A$,
        table.hline(start: 0),
        $3 dot 5$, $2 dot 3$,
        $3 dot 7$, $2 dot 5$,
        $3 dot 13$, $2 dot 11$,
        $3 dot 19$, $2 dot 17$,
        $3 dot 31$, $2 dot 29$,
        $3 dot 43$, $2 dot 41$,
        $3 dot 61$, $2 dot 59$,
        $3 dot 73$, $2 dot 71$,
        $3 dot 103$, $2 dot 101$,
        $3 dot 109$, $2 dot 107$,
        table.hline(start: 0)
      ),
      table(
        stroke: none,
        columns: 2,
        table.hline(start: 0),
        table.vline(start: 0),
        table.cell(colspan: 2, $m=-5$),
        table.vline(start: 0),
        table.hline(start: 0),
        $a$, table.vline(start: 1), $A$,
        table.hline(start: 0),
        $3 dot 13$, $2^2 dot 5$,
        $3 dot 17$, $2^2 dot 7$,
        $3 dot 29$, $2^2 dot 13$,
        $3 dot 37$, $2^2 dot 17$,
        $3 dot 41$, $2^2 dot 19$,
        $3 dot 61$, $2^2 dot 29$,
        $3 dot 89$, $2^2 dot 43$,
        $3 dot 97$, $2^2 dot 47$,
        $3 dot 109$, $2^2 dot 53$,
        $3 dot 137$, $2^2 dot 67$,
        table.hline(start: 0)
      ),
      table(
        stroke: none,
        columns: 5,
        inset: (x, y) => (
          if x == 2 { 0pt }
          else { 5pt }
        ),
        table.hline(start: 0),
        table.vline(start: 0),
        table.cell(colspan: 5, $m=-9$),
        table.hline(start: 0),
        table.vline(start: 0),
        $a$, table.vline(start: 1), $A$, table.vline(start: 1), h(2pt), table.vline(start: 1), $a$, table.vline(start: 1), $A$,
        table.hline(start: 0),
        $3 dot 17$, $2^3 dot 3$, [], $3^2 dot 7$, $2^2 dot 7$,
        $3 dot 73$, $2^3 dot 17$, [], $3^2 dot 11$, $2^2 dot 13$,
        $3 dot 97$, $2^3 dot 23$, [], $3^2 dot 23$, $2^2 dot 31$,
        $3 dot 193$, $2^3 dot 47$, [], $3^2 dot 31$, $2^2 dot 43$,
        $3 dot 241$, $2^3 dot 59$, [], $3^2 dot 43$, $2^2 dot 61$,
        $3 dot 337$, $2^3 dot 83$, [], $3^2 dot 47$, $2^2 dot 67$,
        $3 dot 409$, $2^3 dot 101$, [], $3^2 dot 67$, $2^2 dot 97$,
        $3 dot 433$, $2^3 dot 107$, [], $3^2 dot 71$, $2^2 dot 103$,
        $3 dot 457$, $2^3 dot 113$, [], $3^2 dot 103$, $2^2 dot 151$,
        $3 dot 601$, $2^3 dot 149$, [], $3^2 dot 107$, $2^2 dot 157$,
        table.hline(start: 0)
      )
    ),
    caption: [$p=3$, ダブルB型解の例]
  )
]

#theorem[
  $m:odd, a:odd$ のとき, ダブルB型解の係数 $alpha, beta$ は $alpha=p^f, beta=2^e$ と書ける.
]

#proof[
  まず $a=alpha P, A=beta Q$ の書き方をしたときに, $p | alpha$ が成り立つ.

  というのも, $p divides.not alpha$ を仮定してしまうと, いまダブルB型解の定義より固定された $alpha, beta$ に対して2個以上の解となる $P, Q$ が存在しなければならない.

  しかし, $m:odd, a:odd$ のとき $p divides a$ でなければならないので, $p$ の倍数である素数が複数個存在することになり, 矛盾である.

  同様の理由から, $2 | beta$ も成り立つ.

  したがって, $p divides.not alpha', 2 divides.not beta'$ を満たす $alpha', beta'$ と正整数 $e, f$ を用いて $alpha=p^f alpha', beta=2^e beta'$ と書ける.

  さて, $a=alpha P, A=beta Q$ を定義式である @def-partialmult に代入すると

  #nonumber($ cases(
    p{phi(beta)(Q-1)-m}=alpha P,
    (p-1)(beta Q-m-1)=2phi(alpha)(P-1)
  ) $)

  が得られる.

  さて, これは $P$ と $Q$ に関する連立一次方程式になっている.

  これに2個以上の解が存在するので, この方程式の係数行列の行列式は $0$ でなければならない.

  したがって, $display(mat(delim: "|", p phi(beta), -alpha; (p-1)beta, -2phi(alpha))=-2p phi(alpha)phi(beta)+(p-1)alpha beta=0)$ から, $display((phi(alpha)phi(beta))/(alpha beta)=(p-1)/(2p))$ が成り立つ.

  さて, $phi(alpha)=p^(f-1)(p-1)phi(alpha')$ より, $display(phi(alpha)/alpha=(p-1)/p dot phi(alpha')/alpha')$.

  また, $phi(beta)=2^(e-1)phi(beta')$ より, $display(phi(beta)/beta=1/2 dot phi(beta')/beta')$.

  これらを $display((phi(alpha)phi(beta))/(alpha beta)=(p-1)/(2p))$ に代入すると, $display((phi(alpha')phi(beta'))/(alpha'beta')=1)$ を得, したがって $alpha'=beta'=1$.

  これらを $alpha=p^f alpha', beta=2^e beta'$ に代入すれば, $alpha=p^f, beta=2^e$ を得る.
]

証明内の議論から, @base における $e, f$ は上の定理での $e, f$ と同じ意味で, $L, M$ はそれぞれ $Q, P$ と同じ意味である.

以降は $Q, P$ をそれぞれ $L, M$ と書く.

さて, @base から $display(2^(e-1)+p^(f-1)=(1-m)/2)$ が得られる.

したがって, $p, e, f, m$ は固定されているので, $a=p^f M, A=2^e L$ を定義式である @def-partialmult に代入すると $M$ と $L$ の間の一次関係がわかる.

注意しておかなければならないのは, $f>1$ かつ $p divides m+2^(e-1)$ ならば @base を満たしていてもダブルB型解は存在しない.

というのも, $a=p^f M, A=2^e L$ を @def-partialmult の一番目の式に代入すると $p{2^(e-1)(L-1)-m}=p^f M$ を得るが, これを変形すると $display(L=(p^(f-1)M+m+2^(e-1))/(2^(e-1)))$ となる.

ここで $f>1$ かつ $p divides m+2^(e-1)$ とすると $L$ が $p$ の倍数になってしまい, $p$ の倍数であるような素数は2個以上存在しないからである.

= 重ダブルB型解

$p=3, m=-9$ の場合の解を再掲する.

#align(center)[
  #figure(
    table(
      stroke: none,
      columns: 5,
      inset: (x, y) => (
        if x == 2 { 0pt }
        else { 5pt }
      ),
      table.hline(start: 0),
      table.vline(start: 0),
      $a$, table.vline(start: 1), $A$, table.vline(start: 1), h(2pt), table.vline(start: 1), $a$, table.vline(start: 1), $A$,
      table.vline(start: 0),
      table.hline(start: 0),
      $3 dot 17$, $2^3 dot 3$, [], $3^2 dot 7$, $2^2 dot 7$,
      $3 dot 73$, $2^3 dot 17$, [], $3^2 dot 11$, $2^2 dot 13$,
      $3 dot 97$, $2^3 dot 23$, [], $3^2 dot 23$, $2^2 dot 31$,
      $3 dot 193$, $2^3 dot 47$, [], $3^2 dot 31$, $2^2 dot 43$,
      $3 dot 241$, $2^3 dot 59$, [], $3^2 dot 43$, $2^2 dot 61$,
      $3 dot 337$, $2^3 dot 83$, [], $3^2 dot 47$, $2^2 dot 67$,
      $3 dot 409$, $2^3 dot 101$, [], $3^2 dot 67$, $2^2 dot 97$,
      $3 dot 433$, $2^3 dot 107$, [], $3^2 dot 71$, $2^2 dot 103$,
      $3 dot 457$, $2^3 dot 113$, [], $3^2 dot 103$, $2^2 dot 151$,
      $3 dot 601$, $2^3 dot 149$, [], $3^2 dot 107$, $2^2 dot 157$,
      table.hline(start: 0)
    ),
    caption: $p=3, m=-9$
  )
]

ここでは, 複数個の異なる $alpha=p^f, beta=2^e$ に対してダブルB型解が存在する.

このような解を重ダブルB型解という.

重ダブルB型解が発生する初等的な必要条件は $display(2^(e-1)+p^(f-1)=(1-m)/2)$ でかつ ($f=1$ または $p divides.not m+2^(e-1)$) を満たす $e, f$ が複数個存在することである.

#theorem[
  $p=3$ の場合重ダブルB型解が存在するとき, $m=-9,-21,-33,-69$ のいずれか.
]

#proof[
  #cite(form: "prose", <iannucci2019-2x3y>) より, 非負整数 $x, y$ を用いて $2^x+3^y$ の書き表し方が複数ある整数は

  - $5=2^1+3^1=2^2+3^0$
  - $11=2^1+3^2=2^3+3^1$
  - $17=2^3+3^2=2^4+3^0$
  - $35=2^3+3^3=2^5+3^1$
  - $259=2^4+3^5=2^8+3^1$

  で, それぞれについて $m, e, f$ の組み合わせを計算すると

  - $m=-9, (e, f)=(2, 2), (3, 1)$
  - $m=-21, (e, f)=(2, 3), (4, 2)$
  - $m=-33, (e, f)=(4, 3), (5, 1)$
  - $m=-69, (e, f)=(4, 4), (6, 2)$
  - $m=-517, (e, f)=(5, 6), (9, 1)$

  ここで上記の条件「$f=1$ または $p divides.not m+2^(e-1)$」を $m=-517$ のみ満たさないので, これは除外する.

  よって, 重ダブルB型解が存在するのは $m=-9,-21,-33,-69$ のときのみ.
]

以下は $3<=p<=10000, 1<=e,f<=100$ の範囲で, 重ダブルB型解が存在する $m$ の表である.

#align(center)[

  #figure(
    table(
      columns: 3,
      align: (x, y) => {
        if y == 0 { center }
        else { left }
      },
      table.header(
        table.cell(inset: 9pt, $p$),
        table.cell(inset: 9pt, $m$),
        table.cell(inset: 9pt, $display((1-m)/2)$)
      ),
      $3$, $-9,-21,-33,-69$, $5,11,17,35$,
      $5$, $-17,-65,-257,-265$, $9,33,129,133$,
      $7$, $-17,-129$, $9,65$,
      $11$, $-257$, $129$,
      $13$, $-33$, $17$,
      $17$, $-65$, $33$,
      $29$, $-65$, $33$,
      $31$, $-65,-2049$, $33,1025$,
      $61$, $-129$, $65$,
      $97$, $-257$, $129$,
      $113$, $-257$, $129$,
      $127$, $-257,-32769$, $129,16385$,
      $181$, $-65537$, $32769$,
      $193$, $-513$, $257$,
      $241$, $-513$, $257$,
      $257$, $-1025$, $513$,
      $449$, $-1025$, $513$,
      $509$, $-1025$, $513$,
      $769$, $-2049$, $1025$,
      $1009$, $-2049$, $1025$,
      $1021$, $-2049$, $1025$,
      $2017$, $-4097$, $2049$,
      $4093$, $-8193$, $4097$,
      $7681$, $-16385$, $8193$,
      $7937$, $-16385$, $8193$,
      $8161$, $-16385$, $8193$,
      $8191$, $-16385,-134217729$, $8193,67108865$
    )
  )
]

この表の中で大半を占める $p$ は, $p=2^gamma+1-2^delta$ の形の素数である.

このとき, $display((1-m)/2=2^gamma+1=2^delta+p)$ と書け, どちらも上記の初等的な必要条件を満たす.

特に, $p$ がメルセンヌ素数 $p=2^gamma-1$ であれば, 上の議論で $delta=1$ としたときの重ダブルB型解が現れるだけでなく, $display((1-m)/2=2^(2gamma)+1=2^(gamma+1)+p^2)$ という場合もあり, これも上記の初等的な必要条件を満たす.

よって, メルセンヌ素数に対しては二つの重ダブルB型解を生成する可能性のある (おそらく生成する) $m$ が存在する.

しかし, これ以外にも以下に示すような解が見つかっており, これらの詳しい性質はわかっていない.

(以下の例では $display(mu=(1-m)/2)$ とおいている.)

- $p=3$
  - $m=-21, mu=11=2^3+3^1=2^1+3^2$
  - $m=-69, mu=35=2^5+3^1=2^3+3^3$
- $p=5$
  - $m=-65, mu=33=2^5+5^0=2^3+5^2$
  - $m=-257, mu=129=2^7+5^0=2^2+5^3$
  - $m=-265, mu=133=2^7+5^1=2^3+5^3$
- $p=11$
  - $m=-257, mu=129=2^7+11^0=2^3+11^2$
- $p=181$
  - $m=-65537, mu=32769=2^15+181^0=2^3+181^2$


#set text(lang: "en")

#bibliography(title: [参考文献], "works.bib")
