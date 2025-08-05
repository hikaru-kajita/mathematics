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
  #text(size: 18pt)[$phi^k$ 同値について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

以前, $n~_phi m <==> display(phi(n)/n=phi(m)/m)$ によって定義される $phi$ 同値の条件を解明した.

具体的には, $n~_phi m <==> rad(n)=rad(m)$ がわかった.

今回はその一般化について考察する.

なお, $phi^k (n)$ は $phi$ の $k$ 回合成とし, 特に $phi^0 (n)=n$ と考える.

= 弱い条件

結論から述べると, $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$ が言える.

さて, その証明のためにいくつか補題と補助関数を用意する.

#definition[
  正整数 $n$ に対し, 関数 $phi'$ を $display(phi'(n)=n product_(p^e || n)(1-1/p)^e)$ で定義し, 重複オイラー関数と呼ぶ.
]

$display(phi'(n)=product_(p^e || n)(p-1)^e)$ とも書けることから, $phi'$ は完全乗法的関数である.

つまり, 任意の(互いに素とは限らない)正整数 $a, b$ に対して $phi'(a b)=phi'(a)phi'(b)$ が成り立つ.

#proposition[
  $I$ を正整数とする. 無平方数の正整数からなる数の組 $(alpha_1, alpha_2, ... ,alpha_I)$ について, \
  $display(A=product_(i=1)^I alpha_i)$ とおくと, $display(product_(i=1)^I phi(alpha_i)/alpha_i=(phi'(A))/A)$ が成り立つ.
] <multiplephi>

#proof[
  式は $display(product_(i=1)^I product_(p | alpha_i)(1-1/p)=product_(p^e || A)(1-1/p)^e)$ と書き直せる.

  さて, いま任意の素数 $p$ を取ったとき, $alpha_i$ はすべての $i$ について無平方数であるから, $display(A=product_(i=1)^I alpha_i)$ より \
  $nu_p (A)$ は $p | alpha_i$ を満たす $i$ の個数に等しい.

  つまり, 任意の $p$ について左辺と右辺には同じ個数の $display(1-1/p)$ が積に含まれているので, 式は成り立つ.
]

#proposition[
  任意の正整数 $n, m$ に対し, $display((phi'(n))/n=(phi'(m))/m <==> n=m)$.
] <dupphi-injection>

#proof[
  右から左は明らかであろう. よって示したいのは $display((phi'(n))/n=(phi'(m))/m==>n=m)$ である.

  (1) $gcd(phi'(n), n)=1$ の場合 #indentbox[

  $display((phi'(n))/n)$ が既約分数なので, ユークリッドの補題からある正整数 $k$ を用いて $m=k n, phi'(m)=k phi'(n)$ と書ける.

  さて, 完全乗法性から $phi'(m)=phi'(k n)=phi'(k) phi'(n)$ と書け, したがって $phi'(k)=k$.

  定義式から, $k>1$ とすると $phi'(k)<k$ となってしまうので, $k=1$, したがって $n=m$ が言える.

  ]

  (2) $gcd(phi'(n), n)=n_1>1$ の場合 #indentbox[

    両辺の既約分数形を $display(x/y)$ と書けば, $phi'(n)=n_1 x, n=n_1 y$ が成り立ち, \

    さらにある正整数 $m_1$ で $phi'(m)=m_1 x, m=m_1 y$ を満たすものが存在する.

    ここでは, $display(n/m=n_1/m_1)$ が成り立っている.

    さて, $display((phi'(n))/n=(phi'(n_1 y))/(n_1 y)=(phi'(n_1))/n_1 dot (phi'(y))/y)$.

    同様に, $display((phi'(m))/m=(phi'(m_1))/m_1 dot (phi'(y))/y)$ から, $display((phi'(n_1))/n_1=(phi'(m_1))/m_1).$

    さて, ここで $n_1=n$ とすると $n divides phi'(n)$ だが, 一般に $n>1$ なら $phi'(n)<n$ より $n=1$.

    これは $n_1>1$ に矛盾するので, $n_1 eq.not n$, つまり $n_1<n$ が成り立つことがわかる.

    ここから, $n_1, m_1$ に対して上記の議論をそのまま適用することができる. 

    つまり, (1) から $n_1=m_1$ となるか, もしくはある $n_2<n_1, display((phi'(n_2))/n_2=(phi'(m_2))/m_2\, n_2/m_2=n_1/m_1)$ を満たす正整数の組 $n_2, m_2$ が存在する.

    さて, ここまでの議論をまとめると以下のようになる.

    #align(center)[
      #diagram(
        node((0, 0), $display((phi'(n))/n=(phi'(m))/m)$, name: <base0>),
        node((0, 1), $n=m$, name: <goal>),
        edge(<base0>, <goal>, "->", label: $gcd(n, phi'(n))=1$, label-size: 8pt, label-side: right),

        node((1, 0), $display((phi'(n_1))/n_1=(phi'(m_1))/m_1)$, name: <base1>),
        node((1, 1), $n_1=m_1$, name: <goal1>),
        edge(<base0>, <base1>, "->", label: "otherwise", label-size: 8pt, label-side: right),
        edge(<base1>, <goal1>, "->", $gcd(n_1, phi'(n_1))=1$, label-size: 8pt, label-side: right),

        node((2, 0), $display((phi'(n_2))/n_2=(phi'(m_2))/m_2)$, name: <base2>),
        node((2, 1), $n_2=m_2$, name: <goal2>),
        edge(<base1>, <base2>, "->", label: "otherwise", label-size: 8pt, label-side: right),
        edge(<base2>, <goal2>, "->", $gcd(n_2, phi'(n_2))=1$, label-size: 8pt, label-side: right),

        node((3, 0), $...$, name: <base3>),
        edge(<base2>, <base3>, "->", label: "otherwise", label-size: 8pt, label-side: right),
      )
    ]

    しかし, これは無限に繰り返すことができない; $n>n_1>n_2>...$ となっているので, 無限降下法の要領で, どこかで脱出する必要がある.

    つまり, ある $i$ が存在して, $n_i=m_i$.

    ところが, $display(n/m=n_1/m_1=n_2/m_2=...)$ となっていたので, これは $n=m$ を導く.
  ]
]

さて, 上のふたつから, 次の補題を導くことができる.

#lemma[
  $n, m, k$ を正整数とする. $display((phi^k (n))/n=(phi^k (m))/m)$ と \
  $display(rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m)))$ は同値である.
] <multiphi-equivalent-condition>

#proof[
  $display((phi^k (n))/n)$ を $display(phi(n)/n dot (phi^2 (n))/phi(n) dot (phi^3 (n))/(phi^2 (n)) dot ... dot (phi^k (n))/(phi^(k-1) (n)))$ と変形する.

  さらに, 一般に正整数 $x$ について $display(phi(x)/x=phi(rad(x))/rad(x))$ より, $display((phi^k (n))/n=(phi^k (m))/m)$ は \

  $display(phi(rad(n))/rad(n) dot phi(rad(phi(n)))/rad(phi(n)) dot ... dot phi(rad(phi^(k-1) (n)))/rad(phi^(k-1) (n))=phi(rad(m))/rad(m) dot phi(rad(phi(m)))/rad(phi(m)) dot ... dot phi(rad(phi^(k-1) (m)))/rad(phi^(k-1) (m)))$

  と同値である.

  $N=rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n)), M=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m))$ とおくと, \
  正整数の根基は無平方数であることと @multiplephi から 上の式は $display((phi'(N))/N=(phi'(M))/M)$ に同値で, \
  これは @dupphi-injection から $N=M$ に同値である.
]

主定理の証明の前に, もう一つ補題を証明しておく. (この補題の位置づけは, 主定理の証明の流れを見てからのほうがわかりやすいであろう.)

#lemma[
  $n, m, i$ を正整数, $p$ を素数とする.

  $p | n, p cancel(divides) m, p cancel(divides) phi^i (n), p | phi^i (m)$ が成り立つならば, ある素数 $q>p$ と $0<=j<i$ を満たす整数 $j$ で, \
  $q cancel(divides) phi^j (n)$ かつ $q | phi^j (m)$ を満たすものが存在する.
] <supplylemma>

#[

#set text(size: 9pt)

$phi(n)$ は各 $p^e || n$ について $p^(e-1)(p-1)$ の積である.

つまり, $phi$ を繰り返し適用するにつれて基本的に $p$ の指数は0に達するまで1ずつ減っていき, それが成り立たないのは $p | q-1$ を満たす素数 $q$ が因数のとき.

ここで"供給"される $p$ のべきは $q$ の指数によらない.

いまの設定では, 最初 $p | n, p cancel(divides) m$ で $m$ より $n$ のほうが $p$ を多く含んでいたにも関わらず, $i$ 回 $phi$ を適用したらそれが入れ替わった.

ということは, どこかで $phi^j (n)$ には含まれない $q$ が $phi^j (m)$ に含まれており, その $q$ が $p$ (のべき) を $m$ 側に供給したに違いない, というのが筆者の考えるこの補題の感覚的な説明である.

]

#proof[
  背理法で示す.

  つまり, すべての素数 $q>p$ と $0<=j<i$ を満たす $j$ について $q | phi^j (m)$ ならば $q | phi^j (n)$ を仮定する.

  このとき, すべての $0<=j<=i$ について $nu_p (phi^j (n))>=nu_p (phi^j (m))$ が成り立ってしまうことを帰納法で示す.

  まず, $j=0$ のときは $p | n, p cancel(divides) m$ から $nu_p (phi^j (n))>=1, nu_p (phi^j (m))=0$ よりよい.

  次に, $0<=j=k<i$ のとき $nu_p (phi^k (n))>=nu_p (phi^k (m))$ を仮定しよう. (目標は, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ を示すことである.)

  このとき, $display(nu_p (phi^(k+1) (n))=nu_p (product_(r^e || phi^k (n)) r^(e-1)(r-1))=sum_(r || phi^k (n)) nu_p (r-1)+cases(nu_p (phi^k (n))-1 quad &"if" p | phi^k (n)\,, 0 quad &"otherwise."))$

  (ただし $r$ は素数を指す.)

  さて, 同様の変形が $nu_p (phi^(k+1) (m))$ についてもできるので, 

  1. $display(sum_(r || phi^k (n)) nu_p (r-1)>=sum_(r || phi^k (m)) nu_p (r-1))$
  2. $display(cases(nu_p (phi^k (n))-1 quad &"if" p | phi^k (n)\,, 0 quad &"otherwise.")>=cases(nu_p (phi^k (m))-1 quad &"if" p | phi^k (m)\,, 0 quad &"otherwise."))$

  のふたつを示すことができれば, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ がそこから導かれる.

  1の証明: #indentbox[
    両辺の和の中にある $nu_p (r-1)$ についてだが, $r<=p$ であれば $nu_p (r-1)=0$ であるので, $display(sum_(r || phi^k (n), r>p) nu_p (r-1)>=sum_(r || phi^k (m), r>p) nu_p (r-1) )$ と変形しても同じことである.

    背理法の仮定より, すべての素数 $q>p$ と $0<=j<i$ を満たす $j$ について $q | phi^j (m)==>q | phi^j (n)$.

    いま $0<=k<i$ であるから, 右辺の和に入る $r$ は左辺の和にも入る.

    よって1. が言えた.
  ]

  2の証明: #indentbox[
    簡単のため, $nu_p (phi^k (n))=x, nu_p (phi^k (m))=y$ とおいてしまおう. ($x, y$ は非負整数.)

    すると, 2は $display(cases(x-1 quad &"if" x>=1\,, 0 quad &"otherwise.")>=cases(y-1 quad &"if" y>=1\,, 0 quad &"otherwise."))$ と同じことである.

    いま帰納法の仮定より $nu_p (phi^k (n))>=nu_p (phi^k (m))$ から, $x>=y$.

    よって $x>=1$ かつ $y=0$, $x>=1$ かつ $x>=y>=1$, $x=0$ かつ $y=0$ の3つの場合分けができて, 

    それぞれについて上の不等式が成り立つことは明らかであろう.
  ]

  以上より, $nu_p (phi^(k+1) (n))>=nu_p (phi^(k+1) (m))$ が示せたので, 帰納法よりすべての $0<=j<=i$ について $nu_p (phi^j (n))>=nu_p (phi^j (m)).$

  特に $j=i$ の場合 $nu_p (phi^i (n))>=nu_p (phi^i (m))$ だが, これは $p cancel(divides) phi^i (n), p | phi^i (m)$ というもとの設定に矛盾.

  したがって背理法より, ある素数 $q>p$ と $0<=j<i$ を満たす整数 $j$ で, $q cancel(divides) phi^j (n)$ かつ $q | phi^j (m)$ を満たすものが存在する.
]

#theorem[
  $n, m, k$ を正整数とする. $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$.
]

#proof[
  @multiphi-equivalent-condition より,

  $ rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m)) quad ... (*) $ 
  
  が $rad(n)=rad(m)$ を導くことができればよい.

  いま, $k=1$ の場合は明らかなので $k>1$ の場合を考える.

  背理法で示す; つまり, $rad(n) eq.not rad(m)$ と補題の式を仮定して, 矛盾を示す.

  一般に任意の素数 $p$ と 正整数 $x$ について $p | x <==> p | rad(x)$ に注意すると, $p | n arrow.l.r.double.not p | m$.

  つまり, 一方の素因子ではなく, もう一方の素因子であるような素数 $p_1$ が存在する.

  今回条件は $n$ と $m$ について対称なので, 適切に入れ替えて $p_1 | n$ かつ $p_1 cancel(divides) m$ としよう.

  ここで, 式 $(*)$ において, 根基が無平方数であることから, 任意の素数 $p$ について, $0<=i<k$ の範囲で $p | phi^i (n)$ を満たす $i$ の個数と, $p | phi^i (m)$ を満たす $i$ の個数は一致していなければならない.

  いま $p_1 | n$ かつ $p_1 cancel(divides) m$ より, ある $0<i_1<k$ の範囲の $i_1$ で $p_1 cancel(divides) phi^(i_1) (n)$ かつ $p_1 | phi^(i_1) (m)$ を満たすものが存在する.

  @supplylemma より, ある素数 $p_2>p_1$ と $0<=i_2<i_1$ を満たす整数 $i_2$ で, $p_2 cancel(divides) phi^(i_2) (n)$ かつ $p_2 | phi^(i_2) (m)$ を満たすものが存在する.

  さて, さらに式 $(*)$ において, 両辺に含まれる $p_2$ の個数を比較することにより, ある $0<=i'_2<k, i'_2 eq.not i_2$ を満たす $i'_2$ で $p_2 | phi^(i'_2) (n)$ かつ $p_2 cancel(divides) phi^(i'_2) (m)$ を満たすものが存在する.

  ここで $i_2$ と $i'_2$, $n$ と $m$ を同時に適切に入れ替えて, $i'_2<i_2, p_2 | phi^(i'_2) (n), p_2 cancel(divides) phi^(i'_2) (m), p_2 cancel(divides) phi^(i_2) (n), p_2 | phi^(i_2) (m)$ が成り立つようにする.

  (こうしたことで, 最初の $p_1 | n$ などはもう成り立つかわからなくなるが, これから使用するのは $n, m$ に対して対称な式 $(*)$ と上に述べた条件のみであるから問題ない.)

  さて, @supplylemma の $n, m, i, p$ を $phi^(i'_2) (n), phi^(i'_2) (m), i_2-i'_2, p_2$ でそれぞれ置き換えて再度適用すると, ある素数 $p_3>p_2$ と $i'_2<=i_3<i_2$ を満たす整数 $i_3$ で, $p_3 cancel(divides) phi^(i_3) (n)$ かつ $p_3 | phi^(i_3) (m)$ を満たすものが存在することがわかる.

  この議論は無限に繰り返すことができ, $rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))$ の任意に大きな素因数を構成できてしまう.

  これは矛盾なので, 背理法より, $rad(n)=rad(m)$.
]

= 強い条件

さて, $display((phi^k (n))/n=(phi^k (m))/m ==> rad(n)=rad(m))$ が先の定理の結論であったが, $k>1$ の場合, 逆は必ずしも成り立たない.

つまり, $rad(n)=rad(m)$ は弱い条件である.

より強い条件についても考察することができる:

いま, 正整数 $n, i$ について $nu_p (n)=i$ を満たす素数 $p$ 全体の集合を $S_i (n)$, $nu_p (n)>=i$ を満たす素数 $p$ 全体の集合を $S_(>=i)(n)$ とおく.

#theorem[
  $n, m, k$ を正整数とする. 

  すべての $0<=i<k$ の範囲の整数 $i$ について $S_i (n)=S_i (m)$ が成り立ち, かつ $S_(>=k) (n)=S_(>=k) (m)$ ならば $display((phi^k (n))/n=(phi^k (m))/m)$.
]

#proof[
  条件 "すべての $0<=i<l$ の範囲の整数 $i$ について $S_i (n)=S_i (m)$ が成り立ち, かつ $S_(>=l) (n)=S_(>=l) (m)$" を $n ~_l m$ と書くことにする.

  今, $n~_(l+1) m$ は $n~_l m$ より強い. $n ~_(l+1) m$ を仮定すると, $0<=i<l$ の範囲の整数 $i$ について $S_i (n)=S_i (m)$ が直接言えることはもちろん, $S_(>=l)(n)=S_l (n) union S_(>=l+1) (n)=S_l (m)union S_(>=l+1)(m)=S_(>=l)(m)$ も言えるからである.

  ここから帰納法の要領で, $n~_l m$ が成り立つなら $n~_(l-1) m, n~_(l-2) m, ..., n~_1 m$ も成り立つ.

  さて, 定理の証明に戻ると, @multiphi-equivalent-condition より, $n ~_k m$ を仮定して

  $ rad(n) dot rad(phi(n)) dot ... dot rad(phi^(k-1)(n))=rad(m) dot rad(phi(m)) dot ... dot rad(phi^(k-1)(m)) quad ... (*) $

  を示せばよい.

  これは命題 "任意の正整数 $n, m, l$ について $n ~_l m$ ならば $rad(phi^(l-1) (n))=rad(phi^(l-1) (n))$" (命題Aと呼ぶことにする) がいえれば十分である.

  なぜなら命題 Aが成り立てば, $n ~_k m$ の仮定から $n~_(k-1) m, n~_(k-2) m, ..., n~_1 m$ と合わせて $rad(n)=rad(m), rad(phi(n))=rad(phi(m)), ..., rad(phi^(k-1)(n))=rad(phi^(k-1)(m))$ から式 $(*)$ が示せるからである.

  よって命題 Aを示す.

  しかし, 命題 Aを示すには命題 "任意の正整数 $n, m, l smallspace (l>1)$ について $n~_l m$ ならば $phi(n)~_(l-1) phi(m)$" (命題 B と呼ぶことにする) がいえれば十分である.

  なぜなら命題 Bが成り立てば, $n~_k m$ の仮定から $phi(n)~_(k-1) phi(m), phi^2 (n)~_(k-2) phi^2 (m), ...$ と順に示していって $phi^(k-1) (n)~_1 phi^(k-1) (m)$ が言えるが, 一般に $x~_1 y$ は $rad(x)=rad(y)$ と同値だからである.

  よって命題 Bを示す.

  条件 $n~_l m$ や $phi(n) ~_(l-1) phi(m)$ は $n, m$ について対称であるから, すべての $0<=i<l-1$ の範囲の整数 $i$ に対して $S_i (phi(n)) subset S_i (phi(m))$ かつ $S_(>=l-1) (phi(n)) subset S_(>=l-1)(phi(m))$ が言えれば十分.

  さて, これは任意の素数 $p$ について $nu_p (phi(n))<l-1$ なら $nu_p (phi(n))=nu_p (phi(m))$ で, $nu_p (phi(n))>=l-1$ なら $nu_p (phi(m))>=l-1$ を示せばよい.

  $nu_p (phi(n))<l-1 ==> nu_p (phi(n))=nu_p (phi(m))$ の証明: #indentbox[
    さて, $display(phi(n)=product_(q^e || n)q^(e-1)(q-1))$ より, $display(nu_p (phi(n))=sum_(q | n)nu_p (q-1)+cases(nu_p (n)-1 quad &"if" p | n\,, 0 quad &"otherwise."))$

    いま $l>1$ より $n~_1 m$ から $S_(>=1)(n)=S_(>=1)(m)$ から, $q | n$ を満たす素数 $q$ の集合と $q | m$ を満たす素数 $q$ の集合は等しい, よって $display(sum_(q | n)nu_p (q-1)=sum_(q | m)nu_p (q-1))$.

    よって $display(cases(nu_p (n)-1 quad &"if" p | n\,, 0 quad &"otherwise.")=cases(nu_p (m)-1 quad &"if" p | m\,, 0 quad &"otherwise."))$ がいえれば $nu_p (phi(n))=nu_p (phi(m))$ がいえる.

    ところが $display(cases(nu_p (n)-1 quad &"if" p | n\,, 0 quad &"otherwise.")<=nu_p (phi(n))<l-1)$ より $nu_p (n)<l$.

    いま $n ~_l m$ より, $nu_p (n)=nu_p (m)$ から $nu_p (phi(n))=nu_p (phi(m))$.
  ]

  $nu_p (phi(n))>=l-1 ==> nu_p (phi(m))>=l-1$ の証明: #indentbox[
    先ほどと同様の議論から, $display(sum_(q | n)nu_p (q-1)=sum_(q | m)nu_p (q-1)=Q)$ とおくことにする.

    すると, $display(cases(nu_p (n)-1 quad &"if" p | n\,, 0 quad &"otherwise.")>=l-Q-1 ==> cases(nu_p (m)-1 quad &"if" p | m\,, 0 quad &"otherwise.")>=l-Q-1)$ を示す問題に帰着される.

    だが, いま $n ~_l m$ より $nu_p (n)<l ==> nu_p (m)<l$ は保証されているので, 考えるべきは $nu_p (n)>=l$ の場合である.

    しかしこのとき $nu_p (m)>=l$ が $n ~_l m$ より従うので, $display(cases(nu_p (m)-1 quad &"if" p | m\,, 0 quad &"otherwise.")=nu_p (m)-1>=l-1)$.

    $Q>=0$ より, この式が $l-Q-1$ 以上であることは明らかであろう.
  ]
]


