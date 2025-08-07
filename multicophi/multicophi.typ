#set heading(numbering: "1.")


#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let lemma = thmbox("lemma", "補題", padding: (top: 0em, bottom: 0em))
#let definition = thmbox("definition", "定義", padding: (top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "系", padding: (top: 0em, bottom: 0em))
#let example = thmbox("example", "例", padding: (top: 0em, bottom: 0em))
#let proof = thmproof("proof", "Proof")

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set page(margin: (x: 30pt))

#set text(font: ("New Computer Modern", "Harano Aji Mincho"))

#show heading: it => it + v(10pt)

#let smallspace = [#h(4pt)];
#let even = [even];
#let odd = [odd];
#let prime = [prime];
#let rad = [rad];
#let cophi = $"co"φ$;
#let coφ = cophi;

#let indentbox(body) = context {
  pad(left: 2em, body)
}

#align(center)[
  #text(size: 18pt)[オイラー関数の多重合成に対応する自然な余関数について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= $"co"phi^2$ の定義とその値

オイラー関数 $phi(n)$ には, $"co"phi(n):=n-phi(n)$ で定義される余関数がある.

さて, これの知られている重要な性質を列挙すると:

- $"co"phi(n)=0 <==> n=1$
- $"co"phi(n)=1 <==> n:prime$
- $n:"composite" ==> "co"phi(n)>=sqrt(n)$

つまり, $phi(n)$ は, $n$ が素数という条件ではほぼ $n$ だが, 合成数のときはその差は $sqrt(n)$ 以上になる.

定数 $A, B$ について, $A n-B phi(n)=C$ を求める問題は, $A>B$ のとき簡単すぎ, $A<B$ のとき解けないほど難しい.

余関数はこの丁度いい境目に位置していると考えることができる.

さて, オイラー関数の合成 $phi^2 (n):=phi(phi(n))$ について上のような余関数を定義することを考える.

まずすぐにわかることは, $n-phi(phi(n))$ はうまくいかないであろうということである.

というのも, 一般に大きい $n$ について, $phi(n)$ は偶数であるから, $phi(phi(n))$ は最大でも $n/2$ 程度にしかならない.

そこで, 係数を補って $"co"phi^2 (n):=n-2 phi^2 (n)$ と定義すると, 以降議論するような面白い性質が得られる.

以下に示すのは, 小さい整数の定数 $C$ と, $"co"phi^2 (n)=C$ の解を列挙した表である.

#align(center)[
  #table(
    columns: 2,
    align: (center, left),
    table.header($C$, $n$),
    $-1$, $1$,
    $0$, $2$,
    $1$, $3, 5, 17, 257, 65537$,
    $2$, $2^2$,
    $3$, $7, 11, 23, 47, 59, 83, 107, 167, 179, 227, ...$,
    $4$, $2 dot 3, 2^3$,
    $5$, $3^2, 13, 29, 53, 149, 173, 269, 293, 317, 389, ...$,
    $6$, $2 dot 5$,
    $7$, $3 dot 5, 19$,
    $8$, $2^2 dot 3, 2^4$,
    $9$, $5^2, 41, 89, 137, 233, 569, 809, 857, 1049, 1097, ...$,
  )
]

以降, $p$ はすべて素数を指すものとする.

#theorem[
  $n>2$ ならば, $"co"phi^2(n)>0$.
]

#proof[
  $display(phi(n)=n product_(p | n)(1-1/p))$ の $n$ に $phi(n)$ を代入すると, $display(phi^2 (n)=phi(n) product_(p | phi(n))(1-1/p))$.

  さて, $n>2$ ならば $phi(n)$ は偶数なので, $p=2$ は $p | phi(n)$ を満たす.

  つまり, $display(product_(p | phi(n))(1-1/p)<=1-1/2=1/2)$ より, $display(phi^2 (n)<=1/2 phi(n))$.

  $display("co"phi^2 (n)=n-2phi^2 (n)>=n-2 dot 1/2 phi(n)="co"phi(n))$.

  そして, 一般に $n>1$ のとき $"co"phi(n)>0$ であるから, $"co"phi^2 (n)>="co"phi(n)>0$.
]

さて, $"co"phi^2 (1)=-1, "co"phi^2 (2)=0$ より以下が従う:

- $n=1 <==> "co"phi^2 (n)=-1$
- $n=2 <==> "co"phi^2 (n)=0$
- $n>2 <==> "co"phi^2 (n)>0$

主定理の証明のための補題として, 以下のよく知られた結果を紹介する.

#lemma[
  $n$ が合成数のとき, $phi(n)<=n-sqrt(n)$.
]

#proof[
  $n$ の最小の素因数を $p_0$ とすると, $n$ は合成数なので $p_0<=sqrt(n)$ が成り立つ.

  さて, $display(phi(n)=n product_(p | n)(1-1/p)<=n (1-1/p_0)<=n(1-1/sqrt(n))=n-sqrt(n))$.
]

#theorem[
  $"co"phi^2 (n)=C>0$ が成り立っているとする.

  $n>C^2$ がさらに成り立つとき, $n, C$ は以下のいずれかに当てはまる:

  - $C=1$ で, $n$ はフェルマ素数
  - ある正整数 $e$ を用いて $C=2^e+1$ と書け, $n$ は素数で $display((n-1)/2^e)$ も奇素数.
]

#proof[
  $"co"phi^2 (n)>0$ より, $n>2$.

  このとき $phi(n)$ は偶数なので, $display(2 phi^2 (n)=2phi(n) product_(p | phi(n))(1-1/p)=2phi(n) dot (1-1/2) dot product_(p | phi(n), p eq.not 2) (1-1/p)=phi(n)product_(p | phi(n), p eq.not 2)(1-1/p))$ が成り立つ.

  $n$ が合成数とすると, $phi(n)<=n-sqrt(n)$.

  先の式から $2 phi^2 (n)<=phi(n)$ より, $"co"phi^2 (n)=n-2 phi^2 (n)>=n-(n-sqrt(n))=sqrt(n)$.

  $C>=sqrt(n)$ より, $n<=C^2$.

  よって以降 $n$ が素数の場合のみを考える.

  $n>2$ より, $n$ は奇素数で, $n-1$ は偶数なのである正整数 $e$ と奇数 $L$ を用いて $n-1=2^e L$ と書ける.

  すると, $phi(n)=n-1$ より $display(n-2 phi^2 (n)=n-phi(n)product_(p | phi(n), p eq.not 2)(1-1/p)=n-2^e L product_(p | 2^e L, p eq.not 2)(1-1/p))$.

  ここで $2^e L$ の奇数の素因数は $L$ の素因数と同じなので, $display("co"phi^2 (n)=n-2^e L product_(p | L)(1-1/p)=n-2^e phi(L))$.

  ここで $L$ が合成数であると仮定する.

  すると $"co"phi^2 (n)=n-2^e phi(L)>=n-2^e (L-sqrt(L))=n-2^e L-2^e sqrt(L)=1+2^e sqrt(L)>=1+sqrt(2^e L)>=1+sqrt(n-1)>sqrt(n)$.

  したがってこの場合も $C>sqrt(n)$ より $n<=C^2$ が成り立つ.

  つまり, $n>C^2$ ならば $L$ は1もしくは素数でなければならない.

  $L=1$ の場合, $n-1=2^e$ より $n$ はフェルマ素数である.

  $L$ が素数の場合, $display((n-1)/2^e=L)$ は奇素数で, $C=n-2^e phi(L)=n-2^e (L-1)=n-(n-1)+2^e=1+2^e$.
]

= 一般の $k$ に対応する $"co"phi^k$

一般の $n$ について $phi^2 (n)$ は最大でも $display(n/2)$ ほどにしかならないことから $"co"phi^2 (n):=n-2 phi^2 (n)$ と定義した.

次に, $phi^3 (n)=phi(phi^2 (n))$ は一般の $n$ について $phi^2 (n)$ が偶数であることから $phi^2 (n)$ のさらに半分ほどが限界であろう.

したがって $"co"phi^3 (n):=n-4 phi^3 (n)$ が自然な余関数の定義である.

これらの議論から, 一般の正整数 $k$ について, $"co"phi^k (n):=n-2^(k-1)phi^k (n)$ と定義する.

また便宜上 $phi^0 (n)=n$ とする.

また, $k$ は $n$ に依らない定数とする.

#theorem[
  $k>=1$ とする. $"co"phi^k (n)<=0$ ならば, $phi^k (n)=1$.
] <comultiphi-nonpositive>

#proof[
  対偶法で証明する. つまり, まず $phi^k (n)>=2$ と仮定する.

  すると, $phi(n), phi^2 (n), phi^3 (n), ..., phi^k (n)$ はすべて2以上の整数である.

  さて, $display(phi(n)=n product_(p | n)(1-1/p))$ より $display(phi^2 (n)=phi(n)product_(p | phi(n))(1-1/p))$ と書けた.

  ここから $display(phi^3 (n)=phi^2 (n)product_(p | phi^2 (n))(1-1/p)=phi(n){product_(p | phi(n))(1-1/p)}{product_(p | phi^2 (n))(1-1/p)})$ と書ける.

  この議論を繰り返すと, 一般に $display(phi^k (n)=phi(n) product_(1<=j<k)product_(p | phi^j (n))(1-1/p))$ のように書ける. (これは単純な帰納法によって証明できる.)

  ここで $phi(n), phi^2 (n), ..., phi^k (n)$ がすべて偶数なので, $display(phi^k (n)<=phi(n)product_(1<=j<k)(1-1/2)=phi(n)/(2^(k-1)))$.

  いま $phi(n)$ は偶数なので, $n>2$ から $phi(n)<n$ がわかる.

  したがって $display(phi^k (n)<n/(2^(k-1)))$ より, $2^(k-1)phi^k (n)<n$.

  つまり, $"co"phi^k (n)=n-2^(k-1)phi^k (n)<0$.

  証明したかった命題の対偶が示せたので, 命題は証明された.
]

この逆は成り立たないことに注意. (例: $n=4, k=2$)

#corollary[
  $C$ を整数の定数, $k>=1$ とする.

  $C<=0$ について, $"co"phi^k (n)=C$ の唯一の解は $n=2^(k-1)+C$.  
]

#proof[
  $"co"phi^k (n)=C<=0$ とすると, 先の命題より $phi^k (n)=1$.

  したがって, $"co"phi^k (n)=n-2^(k-1)phi^k (n)=n-2^(k-1)$ より, $n=2^(k-1)+C$ と書ける.

  次に, これが実際に $"co"phi^k (n)=C$ の解であることを示そう.

  先の命題の証明の中で, $phi^k (n)>=2$ ならば $2^(k-1)phi^k (n)<n$ を示していた.

  これはつまり $phi^k (n)>=2$ ならば $n>2^k$ とも言いかえることができる.

  したがって, いま $n=2^(k-1)+C<=2^(k-1)<=2^k$ より $phi^k (n)=1$.

  よって, $"co"phi^k (n)=n-2^(k-1)=(2^(k-1)+C)-2^(k-1)=C$ になっていることが確かめられた.
]

さて, 主定理の証明の前に補助関数を用意し, それについてのいくつかの補題を証明する.

#definition[
  $display(overline(phi)^k (n):=n product_(0<=j<k)product_(p | phi^j (n), p eq.not 2)(1-1/p))$.
]

特に $k=0$ の場合は $overline(phi)^k (n)$ は $n$ と定義される.

#lemma[
  $k>=1$ とする. $n$ が奇数で合成数ならば, $overline(phi)^k (n)<=n-sqrt(n)$.
] <overline-phi-limit>

#proof[
  $display(overline(phi)^k (n)=n product_(0<=j<k)product_(p | phi^j (n), p eq.not 2)(1-1/p)<=n product_(p | n, p eq.not 2)(1-1/p)=phi(n)<=n-sqrt(n).)$
]

#lemma[
  $n, k$ を正整数, $e$ を非負整数とすると, $phi^k (2^e n)=2^f phi^k (n)$ を満たすような非負整数 $f$ が存在する.
] <oddfactor-unchanged>

#proof[
  $e=0$ の場合は $f=0$ とすれば良いことは明らかであろう.

  それ以外の場合を $k$ についての帰納法で証明する.

  まず, $k=1$ の場合について考える.

  $phi(2^e n)$ は $n$ が奇数のとき $2^(e-1)phi(n)$, $n$ が偶数のとき $2^e phi(n)$ に等しい.

  よって命題は $k=1$ の場合に成り立つ.

  次に, $k=k'$ の場合に命題が成り立つと仮定する.

  すると, $phi^k' (2^e n)=2^f phi^k' (n)$ を満たすような非負整数 $f$ が存在する.

  このとき, $phi^(k'+1) (2^e n)=phi(phi^(k') (2^e n))=phi(2^f phi^k' (n))$.

  $k=1$ の場合の命題より, $phi(2^f phi^k' (n))=2^g phi(phi^k' (n))=2^g phi^(k'+1) (n)$ を満たす非負整数 $g$ が存在する.

  帰納法より, 命題は示された.
]

#lemma[
  $n$ を 奇素数とすると, $n-1=2^e L (e>0, L:odd)$ と書ける.

  このとき, $k>=1$ について, $overline(phi)^k (n)=2^e overline(phi)^(k-1) (L)$ が成り立つ.
] <lemma-transition>

#proof[
  $phi(n)=n-1=2^e L$ であることに注意して計算すると,

  $ overline(phi)^k (n)&=n product_(0<=j<k)product_(p | phi^j (n),p eq.not 2)(1-1/p)={n product_(p | n, p eq.not 2)(1-1/p)}product_(1<=j<k)product_(p | phi^j (n),p eq.not 2)(1-1/p) \
  &= phi(n)product_(1<=j<k)product_(p | phi^(j-1)(2^e L),p eq.not 2)(1-1/p)=_*phi(n) product_(1<=j<k)product_(p | phi^(j-1)(L), p eq.not 2)(1-1/p) \
  &= 2^e L product_(0<=j<k)product_(p | phi^j (L),p eq.not 2)(1-1/p)=2^e overline(phi)^(k-1) (L) $.

  なお, $*$ の変形では, @oddfactor-unchanged より, $phi^(j-1)(2^e L)$ と $phi^(j-1)(L)$ の奇素数の素因数が同じであることを利用した.
]

#definition[
  正整数 $n$ と非負整数 $i$ について, $R_i (n)$ を以下のように定義する.

  $ R_i (n):=cases(
      n quad &"if" i=0\,,
      display((R_(i-1)(n)-1)/2^(nu_2 (R_(i-1)(n)-1))) quad &"if" i>0 "and" R_(i-1)(n)>1\,,
      "undefined" quad &"otherwise".
    )
  $
]

$R_i (n)$ が1になるまでは $i$ について $R_i (n)$ が狭義単調減少であることは明らかであろう.

#definition[
  正整数 $n$ と $i$ について, $display(E_i (n):=cases(
    nu_2 (R_(i-1)(n)-1) quad &"if" R_(i-1)(n)>1\,,
    "undefined" quad &"otherwise".
  ))$ と定義する.
]

#definition[
  正整数 $n$ について, $R_i (n)=1$ が成り立つ整数 $i$ を $I(n)$ と定義する.
]

#lemma[
  $n$ と $i$ を正整数とし, $i<=I(n)$ とする.

  このとき, $display(n={sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n))}+R_i (n) dot 2^(sum_(1<=k<=i)E_k (n))).$
] <explicit-expansion-formula>

#proof[
  $i$ についての帰納法で示す.

  $i=1$ のとき, $n=R_0 (n)$ で, $display((R_0 (n)-1)/(2^(E_1 (n)))=R_1(n))$ より $n=1+R_1(n) dot 2^(E_1 (n))$.

  $i<I(n)$ のとき命題が成り立つと仮定すると,

  $ n&={sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n))}+R_i (n)dot 2^(sum_(1<=k<=i)E_k (n)) \
     &={sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n))}+(1+R_(i+1)(n) dot 2^(E_(i+1) (n))) dot 2^(sum_(1<=k<=i)E_k (n)) \
     &={sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n))}+2^(sum_(1<=k<=i)E_k (n))+R_(i+1)(n) dot 2^(sum_(1<=k<=i+1)E_k (n)) \
     &={sum_(1<=j<=i+1)2^(sum_(1<=k<j)E_k (n))}+R_(i+1)(n) dot 2^(sum_(1<=k<=i+1)E_k (n)) $

  つまり $i+1$ のときも命題が成り立つ.

  よって, 数学的帰納法より命題は示された.
]

#theorem[
  $k>1, "co"phi^k (n)=C, phi^(k-1) (n)>1$ が成り立っているとし, $L=min(I(n), k)$ とおく.

  $n>C^2$ がさらに成り立つならば, $0<=j<L$ の範囲のすべての整数 $j$ について $R_j (n)$ が奇素数でなければならない.

  このとき, $display(C=sum_(1<=j<=L)2^(sum_(1<=k<j)E_k (n)))$ が成り立つ.
]

#proof[
  @comultiphi-nonpositive の対偶より, $C>=1$.

  $phi^(k-1) (n)>1$ より, $phi(n), phi^2 (n), ..., phi^(k-1) (n)$ はすべて偶数である.

  さて, @comultiphi-nonpositive での式変形より $display(phi^k (n)=phi(n)product_(1<=j<k)product_(p | phi^j (n))(1-1/p))$.

  いま $phi(n), ..., phi^(k-1) (n)$ はすべて偶数なので $display(2^(k-1)phi^k (n)=phi(n)product_(1<=j<k)product_(p | phi^j (n), p eq.not 2)(1-1/p))$.

  $n=1$ の場合, $phi^(k-1) (n)=1$ なのでそもそも除外する.

  $n$ が合成数ならば, $2^(k-1)phi^k (n)<=phi(n)<=n-sqrt(n)$ より, $"co"phi^k (n)>=n-(n-sqrt(n))=sqrt(n)$.

  したがって $n<=C^2$ なので, 以降 $n$ は素数とする.

  特に $phi(2)=1$ なので $n$ は奇素数である.

  このとき, $display(2^(k-1)phi^k (n)=phi(n)product_(1<=j<k)product_(p | phi^j (n),p eq.not 2)(1-1/p)=n {product_(p | n, p eq.not 2)(1-1/p)}product_(1<=j<k)product_(p | phi^j (n),p eq.not 2)(1-1/p).)$

  これは $overline(phi)^k (n)$ に等しく, よって $"co"phi^k (n)=n-overline(phi)^k (n)$ である.
  
  すると, 以下の命題 (\*) が証明できる:

  #indentbox[
    $i$ を $1<=i<k$ の範囲の整数とする.

    $R_(i-1) (n)$ が奇素数で, $"co"phi^k (n)=n-overline(phi)^(k-i)(R_i (n))2^(sum_(1<=j<=i)E_j (n))$ と表せ, \ $n>C^2$ ならば, 以下のいずれかが成り立つ:

    - $display(R_i (n)=1\, "co"phi^k (n)=sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n)))$
    - $R_i (n):"odd prime", "co"phi^k (n)=n-overline(phi)^(k-i-1)(R_(i+1)(n))2^(sum_(1<=j<=i+1)E_j (n))$
  ]

  命題 (\*) の証明: #indentbox[
    $R_i (n)$ が合成数であると仮定する.

    すると, @overline-phi-limit より $overline(phi)^(k-i)(R_i (n))<=R_i (n)-sqrt(R_i (n))$ であるから, $"co"phi^k (n)>=n-2^(sum_(1<=j<=i)E_j (n)){R_i (n)-sqrt(R_i (n))}$.

    @explicit-expansion-formula から, $display(X=sum_(1<=j<=i)2^(sum_(1<=k<j)E_k (n)))$ とおくと, $n=X+R_i (n) dot 2^(sum_(1<=j<=i)E_j (n))$.

    よって, $"co"phi^k (n)>=X+2^(sum_(1<=j<=i)E_j (n))sqrt(R_i (n))$.

    したがって, $C="co"phi^k (n)>=X+sqrt(2^(sum_(1<=j<=i)E_j (n))R_i (n))=X+sqrt(n-X)$

    $C-X>=sqrt(n-X)$ で, 両辺は正なので2乗して $C^2-2C X+X^2>=n-X$ を得る.

    $C>=X$ から, $C^2-2C X+X^2<=C^2-2 X^2+X^2=C^2-X^2$ より, $C^2-X^2+X>=n$.

    $X>=1$ なので $C^2>=n$ を得る.

    したがって, $n>C^2$ ならば $R_i (n)$ は1もしくは奇素数でなければならない.

    $R_i (n)=1$ の場合, $overline(phi)^(k-i)(R_i (n))=1$ より, $"co"phi^k (n)=n-2^(sum_(1<=j<=i)E_j (n))=X$.

    $R_i (n)$ が奇素数の場合, @lemma-transition より $overline(phi)^(k-i)(R_i (n))=overline(phi)^(k-i-1)(R_(i+1)(n))dot 2^(E_(i+1)(n))$.

    したがって, $"co"phi^k (n)=n-overline(phi)^(k-i-1)(R_(i+1)(n))2^(sum_(1<=j<=i+1)E_j (n))$.
  ]

  さて, 命題 (\*) の前提条件が $i=1$ で成り立つことは明らかであるから, $R_1 (n)$ は1または奇素数.

  $R_1 (n)$ が奇素数の場合は命題 (\*) が $i=2$ でも適用できるので, $R_2(n)$ は1または奇素数. (今はわかりやすさのため $k>=3$ とする)

  まとめると, $k>=3$ の場合は

  - $R_1(n)=1$
  - $R_1(n):"odd prime",R_2(n)=1$
  - $R_1(n):"odd prime",R_2(n):"odd prime"$ の3通りに分けることができる.

  このような議論を繰り返すと, 一般の $k$ について, $n>C^2$ が成り立つには, 次のいずれかが成り立っている必要がある:

  - $I(n)<k$ で, $0<=j<I(n)$ の範囲のすべての整数 $j$ について $R_j (n)$ が奇素数.
  - $I(n)>=k$ で, $0<=j<k$ の範囲のすべての整数 $j$ について $R_j (n)$ が奇素数.

  前者の場合, $display("co"phi^k (n)=sum_(1<=j<=I(n))2^(sum_(1<=k<j)E_k (n)))$.

  後者の場合, $display("co"phi^k (n)=n-R_k (n)2^(sum_(1<=j<=k)E_j (n))=sum_(1<=j<=k)2^(sum_(1<=k<j)E_k (n)))$.

  これらをまとめると証明したかった命題の形になる.
]

この定理の条件「 $0<=j<min(I(n), k)$ の範囲のすべての整数 $j$ について $R_j (n)$ が奇素数」は $n>C^2$ が成り立つための必要条件であるが, 十分条件ではないことに注意.

さて, $n>C^2, phi^(k-1) (n)>1$ が成り立つような $n$ で, $I(n)<k$ であるような $n$ は少ない.

これについて考えよう.

いま, @explicit-expansion-formula より, $display(n=sum_(1<=j<=I(n)+1)2^(sum_(1<=k<j)E_k (n)))$ で, $display(C=sum_(1<=j<=I(n))2^(sum_(1<=k<j)E_k (n)))$ より,

$display(Y=2^(sum_(1<=k<=I(n))E_k (n)))$ とおくと, $n=C+Y$ より $n>C^2$ と $C+Y>C^2$, $Y>C^2-C$ は同値である.

そしてかなり大雑把な評価であるが, $display(C^2-C=C(C-1)>2^(2sum_(1<=k<I(n))E_k (n)))$ より, $display(E_(I(n))(n)>sum_(1<=k<I(n))E_k (n))$ が従う.

さて, $n_(I(n)-1)=2^(E_(I(n)) (n))+1$ はフェルマ素数であるから, ここから $E_1(n), ..., E_(I(n)-1)(n)$ の組み合わせ, ひいては $n$ 自体も限定される.

正確には, フェルマ素数が有限個しか存在しないと仮定したとき, $n>C^2, phi^(k-1) (n)>1, I(n)<k$ を満たす $n$ は($k$ を動かしても)有限個しかないことがわかる.

特に, フェルマ素数が現在知られている $2^2^0+1, 2^2^1+1, 2^2^2+1, 2^2^3+1, 2^2^4+1$ に限られると大胆に仮定すると, 条件を満たす $n$ と $k$ は以下のリストにあるもののみになる.

#align(center)[
  #table(
    columns: 5,
    align: (right, right, right, right, right),
    table.header($n$, $I(n)$, $E_1 (n), ..., E_(I(n))(n)$, $"range of" k$, $C$),
    $3$, $1$, $2$, $[2, 2]$, $1$,
    $5$, $1$, $2$, $[2, 2]$, $1$,
    $17$, $1$, $4$, $[2, 4]$, $1$,
    $257$, $1$, $8$, $[2, 8]$, $1$,
    $65537$, $1$, $16$, $[2, 16]$, $1$,
    $11$, $2$, $1, 2$, $[3, 3]$, $3$,
    $137$, $2$, $3, 4$, $[3, 7]$, $9$
  )
]

これら以外の $n>C^2, phi^k (n)$ を満たす $n$ については, (フェルマ素数が現在知られているものに限ると仮定すれば)すべて $I(n)>=k$ である.
