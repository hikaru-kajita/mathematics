#set heading(numbering: "1.")


#import "@preview/ctheorems:1.1.3": *
#show: thmrules
#let theorem = thmbox("theorem", "定理", padding: (top: 0em, bottom: 0em))
#let lemma = thmbox("lemma", "補題", padding: (top: 0em, bottom: 0em))
#let proposition = thmbox("proposition", "命題", padding: (top: 0em, bottom: 0em))
#let definition = thmbox("definition", "定義", padding: (top: 0em, bottom: 0em))
#let corollary = thmbox("corollary", "系", padding: (top: 0em, bottom: 0em))
#let example = thmbox("example", "例", padding: (top: 0em, bottom: 0em))
#let proof = thmproof("proof", "Proof")

#import "@preview/cetz:0.3.1"
#import "@preview/cetz-plot:0.1.0"
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

#set page(margin: (x: 30pt))

#set text(font: ("New Computer Modern", "Harano Aji Mincho"))

// Make all equations display-style.
// Code borrowed from @frozolotl from https://github.com/typst/typst/discussions/2242#discussioncomment-7112991
#show math.equation.where(block: false): it => {
  if it.has("label") and it.label == <stop-equation-recursion> {
    it
  } else {
    [$display(it)$<stop-equation-recursion>]
  }
}

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
  #text(size: 18pt)[多重オイラー関数の計算について]
  #v(10pt)
  #text(size: 12pt)[梶田光]
  #v(5pt)
  #text(size: 12pt)[#datetime.today().display("[year]/[month]/[day]")]
]

#v(30pt)

= はじめに

オイラー関数の計算は前回の研究で, ルックアップテーブル(LUT)を生成することによって高速に探索できることを示した.

一方, メモリマップトファイルは大きな領域の中のランダムアクセスに弱いため, アクセス箇所が様々な場所に飛ぶ多重オイラー関数の計算には不向きである.

そこで, 今回はそのような問題を解決する, 高速に探索可能なアルゴリズムを考えた.

= 問題の定式化

$n$ について, $k+1$ 個の数からなる組 $(n, φ(n), ..., φ^k (n))$ を $φ^k"-set"$ とよぶ.

この組に対して, $f:φ^k"-set"->{0, 1}$ を計算する関数があるとする. この計算量は実用上 $Theta(1)$ とする.

そして, $1<=n<=N$ の範囲で, $f(n, φ(n), ..., φ^k (n))=1$ を満たす $n$ とその素因数分解を列挙する問題を $φ^k"-problem"$ とよぶ.

#example[
  $n-2 φ^2 (n)=1$ を満たす $1<=n<=10^6$ を計算する問題に対しては, $N=10^6$ ,\
  $f$ を $n-2φ^2 (n)=1$ なら $1$, そうでなければ $0$ を返す関数とすればよい.
]

以降, $N$ は $10^10$ から $10^18$ ほどのオーダーであると仮定する.

このとき, 一般的なコンピュータでは長さ $N$ の配列がRAMに収まらないという点は特筆すべきである.

また, $phi^i (n)=1$ となる最小の $i$ を $R(n)$ と書くと, #cite(form: "prose", <pillai1929function>) より $R(n)<=1+log_2 n$ である.

また, $phi(1)=1$ より, $R(n)$ 以上のすべての $i$ について $phi^i (n)=1$ が成り立つので, それより大きい $k$ の方程式について考えることに意味はない.

したがって, $k$ は最大でも $1+log_2 N$ ほどであると考えてよい.

さて, この問題を考えるときに, メモリマップドファイルを使って計算を高速化することを考える.

つまり, 前もって $1<=n<=N$ のすべての $n$ に対し, $n$ の素因数分解と $φ(n), ..., φ^k (n)$ を記録しておくことで, \
個別の $φ^k"-problem"$ はその参照のみで解くことができるようにする.

以降, このファイルに記録するプロセスをビルド, 個別の $phi^k"-problem"$ をファイルを読み込むことで解くプロセスをロードと呼ぶことにする.

また, 異なる $N$ で実験したい場合があるため, ファイルの中の区間を参照するだけでよいように作成したメモリマップドファイルの中で $n$ は順番に並んでいることが望ましい.

そして, ロード時には $[1, N]$ をRAMに収まる程度の長さに分割し, それぞれの区間について順にファイルの対応する区間をメモリにマップすることになる.

本論文の中では $N$ は常に固定されているものとする.

= $φ^1"-problem"$ について

これは単純に $n, φ(n)$ の組と素因数分解を列挙すればよい.

いま $N$ が大きいことを考えて, 区間篩を利用する.

まず, $φ(n)$ の値だけを求めることを考えると, $φ(n)=n product_(p divides n) (1 - 1/p)$ の公式を利用して, 以下のようにオイラー関数を計算すればよい.

#block(breakable: false)[
  #indentbox[
    *function* _segmented-sieve_(start, end, smallprimes, $f$): #indentbox[
      totients $<-$ [start, start+1, ..., end]

      prime-left $<-$ [start, start+1, ..., end]

      *for* $p$ *in* smallprimes: #indentbox[
        *for all* $m,$ *s.t.* $"start"<=m<="end"$ *and* $p | m$: #indentbox[
          totients[$m - "start"$] $<-$ $"totients"[m - "start"] dot (1-1/p)$

          *while* $p | "prime-left"[m - "start"]$: 
            prime-left[$m - "start"$] $<-$ $"prime-left"[m - "start"] / p$
          
        ]
      ]

      *for* n *in* start...end: #indentbox[
        $p <- "prime-left"[n - "start"]$
        
        *if* $p>1$:
          $"totients"[n - "start"] <- "totients"[n - "start"] dot (1-1/p)$
        
        Write $φ(n)$ as $"totients"[n - "start"]$
      ]
    ]

    $"smallprimes" <- ("list of primes" <= sqrt(N))$ #h(10pt) \// _Use the normal sieve of Eratosthenes_

    *for* (start, end) *in* $(1, "chunk-size"), ("chunk-size"+1, 2 dot "chunk-size"), ..., (..., N)$: #indentbox[
      _segmented-sieve_(start, end, smallprimes)
    ]
  ]
]

ここで, chunk-sizeはその長さを持つ配列がRAMに収まるように設定する ($10^8, 10^9$ など.)

smallprimesは $sqrt(N)$ 以下の素数が含まれているから, prime-leftは1もしくは $sqrt(N)$ より大きい素数である.

よって各 $n$ について, $"totients"[n - "start"]=n product_(p divides n) (1 - 1/p)$ が成り立つ.

以降, 議論が煩雑になるのを防ぐため, 区間篩内部でのアルゴリズムだけ示し, またそこで配列は常にstart \
だけオフセットされているものとする.

さて, 次に素因数分解を取得することについて考える.

通常エラトステネスの篩では各 $n$ ごとに最小素因数 $"spf"[n]$ を記録し, 以下のアルゴリズムによって $n$ のすべての素因数を取得する.

#indentbox[
  $"n_temp" <- n$

  $"factors" <- []$
  
  *while* $"n_temp" > 1$: #indentbox[
    $p <- "spf"["n_temp"]$

    $"factors" <- [..."factors", p]$

    $"n_temp" <- "n_temp"\/n$
  ]
]

一方, この方法はそのままでは今回のメモリマップドファイルに素因数分解を記録し使い回す目的に応用できない. 以下, 理由を説明する.

まず, $"spf"$ 配列はビルドのときに簡単にわかる. 区間篩の中で, 各区間 $["start", "end"]$ 内の任意の $n$ について, 最初に割り切れた素数 $p<=sqrt(N)$ を記録していく.

$n$ が素数であったら, $"spf"[n]$ に $n$ を代入しておけばよい.

問題はそこから $n$ のすべての素因数をどのように取得するかということである.

まず, ビルド時に $"spf"$ だけを記録しておき, ロードのときにそれを利用して $n$ の素因数分解を取得する方法はうまくいかない.

これは, 各 $n$ について, 上のアルゴリズムでの $"n_temp"$ は非常に不規則に, 不連続的に動くからである.

上のアルゴリズムではそのように動く $"n_temp"$ の $"spf"$ を順に追っていかなければならず, とても大きい範囲のマップを作るか頻繁にマップする区間を切り替えなければならない.

したがって, たとえばある正整数 $n$ の素因数分解を知りたい場合に, メモリマップドファイルでマッピングしている($n$ を含む)区間外に, $"n_temp"$ が飛ぶ可能性があり, 結局 $N$ ほどの長さの区間をまとめてマッピングするか, マップする区間を頻繁に切り替えなければならなくなってしまうからである.

もう少しよい方法としては, ビルド中に区間篩を走らせるとき, $n$ のすべての素因数がわかるのだから, (辞書型を用いて $n=p_1^(e_1)p_2^(e_2)...p_k^(e_k)$ に現れる $(p_i, e_i)$ の組を保存するなどして) $n$ の素因数分解をすべてメモリマップドファイルに記録する方法である.

しかしこの方法では, 各 $n$ について素因数は複数個あることがあるので, 結果的にメモリマップドファイルが大きくなってしまう.

これを解決したのが前回証明した定理と, それに依存するアルゴリズムである.

#theorem[
  $n<=N$ とし, $n$ の素因数分解を $n=p_0p_1...p_(m-1) (p_i:prime, p_i<=p_(i+1))$ と書く.

  $i_0$ を $0<=i<=m$ かつ $product_(0<=j<i)p_j<=sqrt(N)$ を満たす最大の $i$, $i_1$ を $i_0<=i<=m$ かつ $product_(i_0<=j<i)p_j<=sqrt(N)$ を満たす最大の $i$ として定義し, $f_0=product_(0<=j<i_0) p_j, f_1=product_(i_0<=j<i_1) p_j, f_2=n/(f_0f_1)$ とおく.

  すると, $f_2$ は必ず $1$ もしくは素数.
]

なお, $n$ や $N$ の値によっては上記の積は空積となることもあるが, 慣習にしたがってその場合は $1$ とする.

下はこの定理の, 前回の証明を改良した証明である.

#proof[
  背理法で示す; $f_2$ が合成数であると仮定する.

  すると $f_2$ は二つの素数の積で割り切ることができる. したがって, $i_1<=m-2, p_(m-2)p_(m-1) | f_2$.

  さて, $f_0f_1p_(m-2)p_(m-1)<=f_0f_1f_2=n<=N$ が成り立つ.

  ところで, $i_1<=m-2$ から $i_0<=i_1<=m-2$. したがって, $p_(i_0), p_(i_1)$ が存在する.

  そして, $i_0, i_1$ の定義より, $f_0p_(i_0)>sqrt(N), f_1p_(i_1)>sqrt(N)$.

  しかし, $p_(i_0)<=p_(m-2), p_(i_1)<=p_(m-2)<=p_(m-1)$ より, $f_0p_(m-2)>sqrt(N), f_1p_(m-1)>sqrt(N)$.

  両辺を掛けると $f_0f_1p_(m-2)p_(m-1)>N$ が得られるが, これは先程示した不等式に矛盾する.
]

さて, これをアルゴリズムに組み込むことを考える. 区間篩の部分は以下のようになる.

#indentbox[
  totients $<-$ [start, start+1, ..., end]

  $f_0 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"start"+1$

  $f_1 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"start"+1$

  *for* $p$ *in* smallprimes: #indentbox[
    *for all* $m,$ *s.t.* $"start"<=m<="end"$ *and* $p | m$: #indentbox[
      totients[$m$] $<-$ $"totients"[m] dot (1-1/p)$

      $"temp_m" <- m$

      *while* $p | "temp_m"$: #indentbox[ 
        $"temp_m" <- "temp_m" / p$

        *if* $f_0[m] dot p <= sqrt(N): f_0[m] <- f_0[m] dot p$

        *else if* $f_1[m] dot p <= sqrt(N): f_1[m] <- f_1[m] dot p$
      ]
    ]
  ]

  *for* n *in* start...end: #indentbox[
    $p <- "prime-left"[n]$
    
    *if* $p>1$:
      $"totients"[n] <- "totients"[n] dot (1-1/p)$
    
    Write $n, "totients"[n], f_0[n], f_1[n]$ to memory-mapped file
  ]
]

ロード時には, $sqrt(N)$ までの素因数分解を計算しておき (これは前計算でもファイルを利用した読み込みでもよい, $sqrt(N)$ は小さいのでボトルネックにはならない), 各区間中の $n$ について $f_0[n], f_1[n]$ の素因数分解を取得し, 素因数分解が自明な $f_2$ と合成すればよい.

このテクニックを部分分解と呼ぶことにする.

= $φ^2"-problem"$ について

$n, φ(n), φ^2 (n)$ と $n$ の素因数分解を列挙する問題である.

ここで重要になるのは, $φ^2 (n)$ が $φ(n)$ と本質的に異なる点がいくつかあることである.

例えば, 乗法性 $gcd(n, m)=1 ==> φ(n m)=φ(n)φ(m)$ は $φ^2$ では成り立たないし, \
$φ^2 (n)=n {product_(p|n) (1-1/p)}{product_(p|φ(n))(1-1/p)}$ を考えたとき, $φ^2 (n)$ と $φ^2 (p n)$ を比較すると因数には $φ(n)$ の \
素因数分解が関わるため非常に複雑である.

一方, 計算するという目的の上であれば, 先ほどの $f_0, f_1, f_2$ に分解するというテクニックを利用することで \
$φ^2 (n)$ を効率的に計算することが可能である. 以下, その方法について議論する.

まず, $n, m$ が互いに素であったとしても, $φ(n), φ(m)$ が互いに素であるとは限らないので, 互いに素な自然数の積で書くことは難しいように見える.

したがって, まず一般に互いに素とは限らない自然数の積のオイラー関数について考える.

下はよく知られた性質である.

#theorem[
  任意の $n, m$ に対し, $d=gcd(n, m)$ とおくと $φ(n m)=φ(n)φ(m)d/φ(d)$.
]

さて, 今 $d divides m$ より, $φ(d) divides phi(m)$.

さらに, $φ(m)d/φ(d)=m{product_(p divides m)(1-1/p)}{product_(p divides d)(1-1/p)}^(-1)=m product_(p divides m, p divides.not d)(1-1/p)<=m$.

つまり, $φ(n m)$ は, それぞれ $n$ と $m$ 以下の整数の積に書くことができる.

したがって, 以下のような関数を考えることができる.

#indentbox[
  *function* _totient-product_(totients, $[n_1, ..., n_k]$): #indentbox[
    *if* $k = 1$: #indentbox[
      *return* $["totients"[n_1]]$
    ]
    *else*: #indentbox[
      $d <- gcd(n_1...n_(k-1), n_k)$

      *return* $[...italic("totient-product")("totients", [n_1, ..., n_(k-1)]), φ(n_k) d/φ(d)]$
    ]
  ]
]

ここでtotientsは $sqrt(N)$ 以下の $n$ についてオイラー関数の値が入るリストで, $n_1, ..., n_k<=sqrt(N)$ とする.

今, $italic("totient-product")("totients", [n_1, ..., n_k])=[n'_1, ..., n'_k]$ と書く.

いくつか例を挙げると,

- $k=1 -> n'_1=φ(n_1)$

- $k=2 -> n'_1=φ(n_1), n'_2=φ(n_2)gcd(n_1,n_2)/φ(gcd(n_1,n_2))$

- $k=3 -> n'_1=φ(n_1), n'_2=φ(n_2)gcd(n_1,n_2)/φ(gcd(n_1,n_2)), n'_3=φ(n_3)gcd(n_1n_2, n_3)/φ(gcd(n_1n_2, n_3))$

など.

ここで, 一般の $k$ について $φ(n_1...n_k)=n'_1...n'_k$ が成り立つ.

さらに, $n'_1<=n_1, ..., n'_k<=n_k$ が成り立つため, 同じtotientsの配列を使いまわしながらこの関数を \
繰り返し適用することで $φ^2(n_1...n_k)$ や $φ^3(n_1...n_k)$ も計算することができる.

これによって, すべての $n<=N$ について, ($f_0, f_1$ は定義上 $sqrt(N)$ 以下であるから) $f_2<=sqrt(N)$ が成り立つならば少しの totients の前計算と $italic("totient-product")$ を利用することによって $phi^2 (n)$ を計算することができる.

したがって, 問題は $f_2>sqrt(N)$ の場合である. (このとき定理から $f_2$ は素数である.)

$f_0f_1$ を $alpha$ と書くと, $n=alpha f_2$ で, $f_2>sqrt(N)>=sqrt(n)$ より, $n$ は $sqrt(n)$ より大きい素因数を1つしか持てないことから $gcd(alpha, f_2)=1$.

したがって $phi(n)=phi(alpha)(f_2-1)$.

さて, ここから $phi^2 (n)$ を計算するには $f_2-1$ の部分分解が必要である.

しかし, これは案外簡単に解決できる.

まず, $alpha=1$ の場合について考える.

このとき, $n=f_2$ であるから, $f_2-1=n-1$ は $n$ の隣にある.

したがって, $sqrt(N)<"start"$ を満たす区間について, $"start"$ が常に非素数となるように調整すれば (これは例えば $"start"$ が奇数ならば1減らすことで解決できる), 任意の $sqrt(N)$ より大きい素数 $n$ について $n-1$ の部分分解は簡単に手に入る.

次に, $alpha>1$ の場合について考える.

このとき, $f_2=n/alpha$ ということは, $"start"/alpha<=f_2<="end"/alpha$ が成り立つ.

また, $alpha f_2<=N$ より, $alpha<=sqrt(N)$.

ここで, 任意の $alpha>1, f_2>sqrt(N), "start"<=n<="end"$ を満たす $n$ について, $f_2$ は $["start"/2, "end"/2], ["start"/3, "end"/3], ["start"/4, "end"/4], ..., ["start"/sqrt(N), "end"/sqrt(N)]$ の区間たちのいずれかに含まれている.

そして, この区間の長さを合計すると $("end"-"start")log N$ ほどのオーダーになり, これは小さい.

したがって, $φ^2 (n)$ も列挙する区間篩内部のアルゴリズムは以下のように書くことができる.

ただし, $sqrt(N)$ 以下の $n$ について $φ(n)$ の値を持つtotientsは, 区間篩の前計算でsmallprimesとともに計算しておく.

また長さ $N$ の $"primechain"$ という配列を初期化しておく. (これはメモリマップして利用する.)

$"primechain"$ のそれぞれの要素は2つの32ビット符号なし整数を書くサイズがあり, 0で初期化されているものとする.

(具体的には, $f_0$ と $f_1$ のペアを書き込み, $f_0, f_1<=sqrt(N)$ で $N$ は実用上 $2^64~10^19$ 未満としてよいので $f_0, f_1$ は32ビットに収まることになる.)

#indentbox[
  $"low_start" <- "start"$

  *if* $"start": odd$ and $"start">1$: $"low_start" <- "start" - 1$ 

  $f_0 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"low_start"+1$

  $f_1 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"low_start"+1$

  Memory-map interval $[floor("start"/2), floor("end"/2)], [floor("start"/3), floor("end"/3)], [floor("start"/4), floor("end"/4)], ..., [floor("start"/sqrt(N)), floor("end"/sqrt(N))]$ of primechain

  *for* $p$ *in* smallprimes: #indentbox[
    *for all* $m,$ *s.t.* $"low_start"<=m<="end"$ *and* $p | m$: #indentbox[
      $"m_temp" <- m$

      *while* $p | "m_temp"$: #indentbox[
        $"m_temp" <- "m_temp" / p$

        *if* $f_0[m] dot p <= sqrt(N): f_0[m] <- f_0[m] dot p$

        *else if* $f_1[m] dot p <= sqrt(N): f_1[m] <- f_1[m] dot p$
      ]
    ]
  ]

  *for* n *in* start...end: #indentbox[
    $f_2 <- n/(f_0[n]f_1[n])$

    *if* $f_2<=sqrt(N)$: #indentbox[
      $[f'_0, f'_1, f'_2]<-italic("totient-product")("totients", [f_0[n], f_1[n], f_2])$

      $[f''_0, f''_1, f''_2]<-italic("totient-product")("totients", [f'_0, f'_1, f'_2])$

      Write $phi(n)=f'_0f'_1f'_2, phi^2 (n)=f''_0f''_1f''_2$ to file
    ]
    
    *else if* $f_0[n]=f_1[n]=1$: #h(10pt) \/\/ $n$ is a prime $>sqrt(N)$ #indentbox[
      $[f'_0, f'_1, f'_2]<-italic("totient-product")("totients", f_0[n-1], f_1[n-1], (n-1)/(f_0[n-1]f_1[n-1]))$

      Write $phi(n)=n-1, phi^2 (n)=f'_0f'_1f'_2$ to file

      Write tuple $f_0[n-1], f_1[n-1]$ to $"primechain"[n]$
    ]

    *else*: #indentbox[
      $alpha <- f_0[n]f_1[n]$

      $[f'_0, f'_1] <- "primechain"[f_2]$

      $f'_2 <- (f_2-1)/(f'_0f'_1)$

      Write $phi(n)="totient"[alpha](f_2-1)$

      *if* $f'_2<=sqrt(N)$: #indentbox[
        Write $phi^2 (n)=italic("totient-product")("totients", ["totient"[alpha], f'_0, f'_1, f'_2)$
      ]
      *else*: #indentbox[
        Write $phi^2 (n)=italic("totient-product")("totients", ["totient"[alpha], f'_0, f'_1)(f'_2-1)$
      ]
    ]
  ]
]

= $phi^k"-problem"$ について

適当な区間 $["start", "end"]$ 内の正整数 $n$ の $phi(n), phi^2 (n), ..., phi^k (n)$ までを計算するには, 区間 $["start", "end"]$ を見ている時点でどのような情報が得られればよいかを考える.

まず, $n$ の分解 $n=f_0f_1f_2$ を考える.

もし $f_2<=sqrt(N)$ であれば, $[f_0, f_1, f_2]$ に _totient-product_ を繰り返し適用し続ければよい.

それ以外の場合, $alpha=f_0f_1$ とおくと $alpha=n/f_2<N/sqrt(N)=sqrt(N)$ で, $phi(n)=phi(alpha f_2)=phi(alpha)(f_2-1)$ である.

$phi^2 (n)$ を計算するためには, $f_2-1$ の分解 $f_2-1=f'_0f'_1f'_2$ が必要である.

もし $f'_2<=sqrt(N)$ であれば, $phi(n)=phi(alpha)f'_0f'_1f'_2$ は $sqrt(N)$ 以下の正整数の積で書けるから_totient-product_を繰り返し適用すればよい.

それ以外の場合, $alpha'=phi(alpha)f'_0f'_1$ とおくと $k'=phi(n)/f'_2<n/sqrt(N)<=N/sqrt(N)=sqrt(N)$ で, $phi^2 (n)=phi(alpha')(f'_2-1)$.

$phi^3 (n)$ を計算するためには, $f'_2-1$ の分解 $f'_2-1=f''_0f''_1f''_2$ が必要である.

もし $f''_2<=sqrt(N)$ であれば, $phi^2 (n)=phi(alpha')f''_0f''_1f''_2$ は $sqrt(N)$ 以下の正整数の積で書けるから_totient-product_を繰り返し適用すればよい.

それ以外の場合, $alpha''=phi(alpha')f''_0f''_1f''_2$ とおくと $alpha''=(phi^2 (n))/f''_2<n/sqrt(N)<=N/sqrt(N)=sqrt(N)$ で, $phi^3 (n)=phi(alpha'')(f''_2-1)$.

$f'''$ を $f^((3))$, $f''''$ を $f^((4))$ などして表記すると, $phi^k (n)$ を計算するためには $f^((k-1))_0, f^((k-1))_1, f^((k-1))_2$ までが必要である.

さて, アルゴリズムの議論のために2つ命題を証明しておく.

#lemma[
  $n, i$ を正整数とし, $f_2, f'_2, f''_2, ..., f^((i))_2$ がすべて $sqrt(N)$ より大きいとする.

  $beta^((j)):=f^((j))_0f^((j))_1,B_j:=product_(m=1)^j beta^((j))$ とおくと $n=beta(f^((i))_2B_i+sum_(m=0)^(i-1)B_m)$.

  なお $B_0$ は $1$ と定義する.
]

#proof[
  $i$ についての帰納法で証明する.

  $i=1$ の場合は $n=f_0 f_1 f_2=beta (1+f'_0 f'_1 f'_2)=beta(f'_2beta'+B_0)=beta(f'_2B_1+B_0)$ よりよい.

  $i$ の場合について命題が成り立っていると仮定すると,

  $n=beta(f_2^((i))B_i+sum_(m=0)^(i-1)B_m)=beta((1+beta^((i+1))f_2^((i+1)))B_i+sum_(m=0)^(i-1)B_m)=beta(f_2^((i+1))B_(i+1)+sum_(m=0)^i B_m)$ より $i+1$ の場合も成り立つ.
]

#theorem[
  $n, i$ を正整数とし, $f_2, f'_2, f''_2, ..., f^((i))_2$ をすべて $sqrt(N)$ より大きい奇素数とする.

  先の命題と同様に $beta^((i)), B_i$ を定義すると $f_2^((i))=floor(n/(beta B_i))$.
]

#proof[
  $f_2^((i))=floor(n/(beta B_i))$ は $f_2^((i))=floor(f_2/B_i)$ と同値なので, これを証明する.

  まず, 先の命題から $f_2=f_2^((i))B_i+sum_(m=0)^(i-1)B_m$ が得られた.

  両辺を $B_i$ で割って $f_2/B_i=f_2^((i))+sum_(m=0)^(i-1)B_m/B_i$ を得る.

  さて, 任意の $0<=m<i$ について, $B_(m+1)=beta^((m+1))B_m$ であるが, $f_2^((m))-1=beta^((m+1))f_2^((m+1))$ で $f_2^((m)), f_2^((m+1))$ は奇素数なので $beta^((m+1))$ は偶数で, これは $2$ 以上.

  したがって任意の $0<=m<i$ について $B_(m+1)>=2 B_m$ である.

  ここから $B_m/B_i=B_m/B_(m+1) dot B_(m+1)/B_(m+2) dot ... dot B_(i-1)/B_i<=(1/2)^(i-m)$ が従うので, $0<=sum_(m=0)^(i-1)B_m/B_i<=sum_(m=0)^(i-1)(1/2)^(i-m)<1$.

  よって, $f_2^((i))<=f_2/B_i<f_2^((i))+1$ から, $f_2^((i))=floor(f_2/B_i)$ が示された.
]

さて, この定理の重要な点は, どんなに大きい $i$ を取ってきても, $f_2^((i))$ が $sqrt(N)$ より大きければ, $f_2^((i))$ は必ずharmonic mapの範囲に含まれているということである (このとき $beta B_i<=sqrt(N)$ は明らかであろう.)

したがって, $phi^k (n)$ までを計算するために必要な情報は, すべて_totient-product_とprimechainのharmonic mapから得られることになる.

#[
  #set text(size: 8pt)

  これはGPT-5との議論から発展した.

  もともと筆者は $f_2^((i))$ はprimechainの範囲外であると思い込んでおり, そのため最初に考えていたアルゴリズムは各primechainの要素には長さ $k-1$ の配列を持たせておき, $f_2$ が区間に含まれているときに $f'_2$ のprimechainをコピーするという方法を取っていた.

  そのため, 空間計算量は $O(k sqrt(N)log N)$ になっていた.

  しかし, GPT-5 にそのアルゴリズムの概要を入力し, 発展のアイデアを出すよう指示したところ, GPT-5は $f_2^((i))$ が常にprimechainの範囲*内*にあると思い込んでおり (証明はなかったし, おそらく内部でも証明はしていないであろう), primechainの $f_2$ 番目には $f'_0, f'_1$ のみを書き, primechain全体を単連結リストの森のように扱うことを考案した.

  筆者はこの議論から先の補題と定理に気づき, 現在のアルゴリズムを構築した.
]

以上を踏まえ, $phi^k"-problem"$ のためのファイルをビルドするときの区間篩のアルゴリズムを考えると以下のようになる.

なお, primechain は $phi^2"-problem"$ のときと同様, 長さ $N$ の配列とする.

#align(center)[
  #block[
    #align(left)[
      #indentbox[
        #set par.line(numbering: i => i, number-clearance: -10pt)

        $"low_start" <- "start"$

        *if* $"start": odd$ and $"start">1$: $"low_start" <- "start" - 1$ 

        $f_0 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"low_start"+1$

        $f_1 <- [1, 1, ..., 1] #h(10pt) \/\/ "Length": "end"-"low_start"+1$

        Memory-map interval $[floor("start"/2), floor("end"/2)], [floor("start"/3), floor("end"/3)], [floor("start"/4), floor("end"/4)], ..., [floor("start"/sqrt(N)), floor("end"/sqrt(N))]$ of primechain

        *for* $p$ *in* smallprimes: #indentbox[
          *for all* $m,$ *s.t.* $"low_start"<=m<="end"$ *and* $p | m$: #indentbox[
            $"m_temp" <- m$

            *while* $p | "m_temp"$: #indentbox[
              $"m_temp" <- "m_temp" / p$

              *if* $f_0[m] dot p <= sqrt(N): f_0[m] <- f_0[m] dot p$

              *else if* $f_1[m] dot p <= sqrt(N): f_1[m] <- f_1[m] dot p$
            ]
          ]
        ]

        *for* n *in* start...end: #indentbox[
          $f_2 <- n/(f_0[n]f_1[n])$

          *if* $f_2<=sqrt(N)$: #indentbox[
            $"seq"<-[f_0[n], f_1[n], f_2]$

            *for* $i$ *in* 1..$k$: #indentbox[
              $"seq"<-italic("totient_product")("totients", "seq")$

              Write $phi^i (n)="seq"[0] dot "seq"[1] dot "seq"[2]$
            ]

            *continue*
          ]
          
          *if* $f_0[n]=f_1[n]=1$: #h(10pt) \/\/ $n$ is a prime $>sqrt(N)$ #indentbox[
            $"primechain"[n]<-[f_0[n-1], f_1[n-1]]$
          ]

          $alpha^((i-1))<-f_0[n]f_1[n]$

          $f_2^((i-1))<-f_2$

          *for* $i$ in 1...$k$: #indentbox[
            Write $phi^i (n)="totients"[alpha^((i-1))](f_2^((i-1))-1)$

            *if* $i=k$: *break*

            $[f_0^((i)), f_1^((i))]<-"primechain"[f_2^((i-1))]$

            $f_2^((i))<- (f_2^((i-1))-1)/(f_0^((i))f_1^((i)))$

            *if* $f_2^((i))<=sqrt(N)$: #indentbox[
              $"seq"<-["totients"[alpha^((i-1))], f_0^((i)), f_1^((i)), f_2^((i))]$

              *for* $j$ in $i+1$...$k$: #indentbox[
                $"seq"<-italic("totient-product")("totients", "seq")$

                Write $phi^j (n)="seq"[0] dot "seq"[1] dot "seq"[2] dot "seq"[3]$
              ]

              *break*
            ]

            $alpha^((i-1))<-"totients"[alpha^((i-1))]f_0^((i))f_1^((i))$

            $f_2^((i-1))<-f_2^((i))$
          ]
        ]
      ]
    ]
  ]
]

$k=O(log N)$ に注意すると, 一つの区間について, 空間計算量は $O(("end"-"start")k log N)$, 時間計算量は $O(("end"-"start")log N)$.

全体のビルドのアルゴリズムについては, 区間の長さを $sqrt(N)$ 程度とすると空間計算量が $O(sqrt(N)log N)$, 時間計算量が $O(k N log N)$ ($gcd$ の計算がボトルネック), 必要なディスクの容量は $O(k N)$.

そして, 内部-外部メモリ間のI/Oは $O(N(k+log N) dot 1/B)$ である. (なお, $B$ は1ブロックの長さ.)

なお, ルックアップテーブルを作らず, 単一の $phi^k"-problem"$ のみを計算するアルゴリズムも考えられる.

その場合, 時間・空間計算量は変わらないが, ディスクに置くのが長さ $N$ のprimechainのみでよくなり, ディスクの容量 $O(N)$, I/O $O((k N)/B)$ で済む.

この問題を解く単純なアルゴリズムとして, $phi(n)$ の配列を作り,
- $phi^2 (n)$ を得るために $(n, phi(n))$ のペアを $phi(n)$ の昇順で外部ソート
- $phi^3 (n)$ を得るために $(n, phi(n), phi^2 (n))$ のタプルを $phi^2 (n)$ の昇順で外部ソート
- ...
と繰り返してランダムアクセスを回避する方法が考えられる.

しかし, これは空間計算量を $O(M)$ に抑えたとき時間計算量 $O(k N log N)$, ディスクの容量 $O(k N)$ だが I/O $O(k N/B log_(M/B)(N/B))$ となり, こちらのほうが大きい.

= 各種最適化

以下では, 前章の最後に示したアルゴリズムについて議論する.

== 並列化

このアルゴリズムは並列化も可能である.

並列化が効率に貢献する主な箇所は2箇所ある.

一つは区間 $["low_start", "end"]$ 内の各 $n$ について $f_0, f_1$ を計算する6-12行目の箇所である.

データの競合を防ぐため, $m$ に関するループを並列化することが限界と思われる.

二つ目は $phi(n), phi^2 (n), ..., phi^k (n)$ を計算する13-39行目の $n$ に関するループ全体である.

注意しなければならないのは, このループ (*for* $n$ in $"start"..."end"$: ) 内では基本的に $n$ に関するポインタのみ書き込み/読み込みを行うが, primechainでは離れた場所のポインタの読み込みを行うのでデータ競合が発生しうるということである.

つまり, 30行目で primechain から整数の組を読み込んでいるが, これは $f_2$ での primechain への書き込み (22-24行目) が行われた後でなければならず, 愚直な並列化ではこれが成り立たない可能性がある.

したがって, 13-39行目のループ全体を並列化する際には, $"start"$ と $"end"$ を調整して, 読み込みと書き込みの順番の整合性が取れるようにする必要がある.

具体的には, $["start", "end"]$ 内のすべての整数 $n$ について, $n$ に対応する $f_2=n/(f_0[n]f_1[n])$ が $sqrt(N)$ を超えるとき, $"primechain"[f_2]$ は $["start", "end"]$ の区間の処理の前に計算されていなければならない.

これを解決する単純な方法は常に $"start" * 2 > "end"$ とすることで, 

これは, 以下のように $"start"$ と $"end"$ を決めることで解決できる:

#indentbox[
  $"start" <- 0$

  $"end" <- floor(sqrt(N))$

  *loop*: #indentbox[
    $"start" <- "end" + 1$

    *if* $"start" > N$: *break*

    $"end" <- min("end" + "chunk-size", 2 * "end" + 1, N)$

    $italic("segmented-sieve")("start", "end", "smallprimes")$
  ]
]

この $"end" <- min("end" + "chunk-size", 2 * "end" + 1, N)$ が重要である.

この処理をする直前, $"start"$ は $"end" + 1$ であるから, $"end"$ が $2 * "end" + 1$ を超えないようにすることで $"start" * 2 > "end"$ が成り立つようにできる.

== primechainの長さの削減

先のアルゴリズムで, 配列primechainの添字には素数しか現れない.

したがって, 単純な効率化のアイデアとしては, primechainの2以上の偶数の部分を省くということである.

このとき, $"compress"(n):=ceil(n / 2)$ のように定義した関数を用いて, primechainの長さを $"compress"(N)+1$ に設定, 区間 $["start", "end"]$ を計算するときのメモリマップする範囲を $[floor("start"/2), floor("end"/2)], [floor("start"/3), floor("end"/3)], ..., [floor("start"/sqrt(N)), floor("end"/sqrt(N))]$ から \
$[floor("compress"("start")/2), floor("compress"("end")/2)], ..., [floor("compress"("start")/sqrt(N)), floor("compress"("end")/sqrt(N))]$ に変更し, すべてのアクセス $"primechain"[p]$ を $"primechain"["compress"(p)]$ に置き換えることができる.

すると, primechainに必要な長さや空間計算量はほぼ半分に削減できる.

同様に3の倍数, 5の倍数なども除くように, 添字を圧縮するcompress関数を定義することができる.

これをより一般に考え, wheel sieveのような考え方を利用する.

今, 素数を小さい方から順に $m$ 個とって $p_0, p_1, ..., p_(m-1)$ とする.

そして $m$ は $P=p_0p_1...p_(m-1)<=sqrt(N)$ を満たす最大の $m$ とおく.

$S={p_0, p_1, ..., p_(m-1)} union {n | n>p_(m-1), gcd(n, P)=1}$ とおけば, $S$ は素数全体の集合を含む.

そして, $"compress"(n)$ は $sharp{p in S | p<=n}-1$ とおけばよい.

したがって, $"compress"(n)$ を計算するアルゴリズムは以下のようになる:

#indentbox[
  $C_"small" = [1, 1, ..., 1, 1] #h(10pt) \/\/ "Length": P+1$

  $C_"large" = [1, 1, ..., 1, 1] #h(10pt) \/\/ "Length": P+1$

  $C_"small" [0] <- 0; C_"small" [1] <- 0; C_"small" [P] <- 0$

  $C_"large" [0] <- 0; C_"large" [P] <- 0$

  *for* $p$ in $[p_0, p_1, ..., p_(m-1)]$: #indentbox[
    $C_"large" [p] <- 0$

    *for all* $j$ *s.t.* $2*p<=j<P, p | j$: #indentbox[
      $C_"small" [j] <- 0; C_"large" [j] <- 0$
    ]
  ]

  *for* $n$ in $0..P-1$: #indentbox[
    $C_"small" [n+1] <- C_"small" [n] + C_"small" [n+1]$

    $C_"large" [n+1] <- C_"large" [n] + C_"large" [n+1]$
  ]

  *function* $"compress"(n)$: #indentbox[
    *if* $n <= P$: *return* $C_"small" [n] - 1$

    *else*: *return* $C_"small" [P] + C_"large" [P] * (floor(n / P) - 1) + C_"large" [n mod P] - 1$
  ]
]

これを利用すると, 全体の空間計算量を $O((sqrt(N)log N)/(log log N))$に抑えられる.

#bibliography("works.bib", style: "ieee", title: "参考文献")
