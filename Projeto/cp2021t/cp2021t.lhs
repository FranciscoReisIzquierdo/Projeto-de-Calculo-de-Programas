\documentclass[a4paper]{article}
\usepackage[a4paper,left=3cm,right=2cm,top=2.5cm,bottom=2.5cm]{geometry}
\usepackage{palatino}
\usepackage[colorlinks=true,linkcolor=blue,citecolor=blue]{hyperref}
\usepackage{graphicx}
\usepackage{cp2021t}
\usepackage{subcaption}
\usepackage{adjustbox}
\usepackage{color}
\definecolor{red}{RGB}{255,  0,  0}
\definecolor{blue}{RGB}{0,0,255}
\def\red{\color{red}}
\def\blue{\color{blue}}
%================= local x=====================================================%
\def\getGif#1{\includegraphics[width=0.3\textwidth]{cp2021t_media/#1.png}}
\let\uk=\emph
\def\aspas#1{``#1"}
%================= lhs2tex=====================================================%
%include polycode.fmt 
%format (div (x)(y)) = x "\div " y
%format succ = "\succ "
%format ==> = "\Longrightarrow "
%format map = "\map "
%format length = "\length "
%format fst = "\p1"
%format p1  = "\p1"
%format snd = "\p2"
%format p2  = "\p2"
%format Left = "i_1"
%format Right = "i_2"
%format i1 = "i_1"
%format i2 = "i_2"
%format >< = "\times"
%format >|<  = "\bowtie "
%format |-> = "\mapsto"
%format . = "\comp "
%format .=?=. = "\mathbin{\stackrel{\mathrm{?}}{=}}"
%format (kcomp (f)(g)) = f "\kcomp " g
%format -|- = "+"
%format conc = "\mathsf{conc}"
%format summation = "{\sum}"
%format (either (a) (b)) = "\alt{" a "}{" b "}"
%format (frac (a) (b)) = "\frac{" a "}{" b "}"
%format (uncurry f) = "\uncurry{" f "}"
%format (const f) = "\underline{" f "}"
%format TLTree = "\mathsf{TLTree}"
%format (lcbr (x)(y)) = "\begin{lcbr}" x "\\" y "\end{lcbr}"
%format (split (x) (y)) = "\conj{" x "}{" y "}"
%format (for (f) (i)) = "\for{" f "}\ {" i "}"
%format B_tree = "\mathsf{B}\mbox{-}\mathsf{tree} "
\def\ana#1{\mathopen{[\!(}#1\mathclose{)\!]}}
%format <$> = "\mathbin{\mathopen{\langle}\$\mathclose{\rangle}}"
%format (cataA (f) (g)) = "\cata{" f "~" g "}_A"
%format (anaA (f) (g)) = "\ana{" f "~" g "}_A"
%format (cataB (f) (g)) = "\cata{" f "~" g "}_B"
%format (cata (f)) = "\cata{" f "}"
%format (anaB (f) (g)) = "\ana{" f "~" g "}_B"
%format Either a b = a "+" b 
%format fmap = "\mathsf{fmap}"
%format NA   = "\textsc{na}"
%format NB   = "\textsc{nb}"
%format inT = "\mathsf{in}"
%format outT = "\mathsf{out}"
%format Null = "1"
%format (Prod (a) (b)) = a >< b
%format fF = "\fun F "
%format e1 = "e_1 "
%format e2 = "e_2 "
%format Dist = "\fun{Dist}"
%format IO = "\fun{IO}"
%format BTree = "\fun{BTree} "
%format LTree = "\mathsf{LTree}"
%format inNat = "\mathsf{in}"
%format (cataNat (g)) = "\cata{" g "}"
%format (cataNotEmptyList (g)) = "\cata{" g "}"
%format (cataExpAr (g)) = "\cata{" g "}"
%format inNotEmptyList = "\mathsf{in}"
%format inExpAr = "\mathsf{in}"
%format Nat0 = "\N_0"
%format Rational = "\Q "
%format toRational = " to_\Q "
%format fromRational = " from_\Q "
%format muB = "\mu "
%format (frac (n)(m)) = "\frac{" n "}{" m "}"
%format (fac (n)) = "{" n "!}"
%format (underbrace (t) (p)) = "\underbrace{" t "}_{" p "}"
%format matrix = "matrix"
%%format (bin (n) (k)) = "\Big(\vcenter{\xymatrix@R=1pt{" n "\\" k "}}\Big)"
%format `ominus` = "\mathbin{\ominus}"
%format % = "\mathbin{/}"
%format <-> = "{\,\leftrightarrow\,}"
%format <|> = "{\,\updownarrow\,}"
%format `minusNat`= "\mathbin{-}"
%format ==> = "\Rightarrow"
%format .==>. = "\Rightarrow"
%format .<==>. = "\Leftrightarrow"
%format .==. = "\equiv"
%format .<=. = "\leq"
%format .&&&. = "\wedge"
%format cdots = "\cdots "
%format pi = "\pi "
%format (curry (f)) = "\overline{" f "}"
%format (cataLTree (x)) = "\llparenthesis\, " x "\,\rrparenthesis"
%format (anaLTree (x)) = "\mathopen{[\!(}" x "\mathclose{)\!]}"
%format delta = "\Delta "

%---------------------------------------------------------------------------

\title{
       	C??lculo de Programas
\\
       	Trabalho Pr??tico
\\
       	MiEI+LCC --- 2020/21
}

\author{
       	\dium
\\
       	Universidade do Minho
}


\date\mydate

\makeindex
\newcommand{\rn}[1]{\textcolor{red}{#1}}
\begin{document}

\maketitle

\begin{center}\large
\begin{tabular}{ll}
\textbf{Grupo} nr. & 77 
\\\hline
a93241 & Francisco Reis Izquierdo	
\\
a93273 & Jos?? Pedro Martins Magalh??es
\\
a89526 & Duarte Augusto Rodrigues Lucas	
\\
a93185 & Carlos Filipe Almeida Dias
\end{tabular}
\end{center}

\section{Pre??mbulo}

\CP\ tem como objectivo principal ensinar
a progra\-ma????o de computadores como uma disciplina cient??fica. Para isso
parte-se de um repert??rio de \emph{combinadores} que formam uma ??lgebra da
programa????o (conjunto de leis universais e seus corol??rios) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto ??,
agregando programas j?? existentes.
  
Na sequ??ncia pedag??gica dos planos de estudo dos dois cursos que t??m
esta disciplina, opta-se pela aplica????o deste m??todo ?? programa????o
em \Haskell\ (sem preju??zo da sua aplica????o a outras linguagens 
funcionais). Assim, o presente trabalho pr??tico coloca os
alunos perante problemas concretos que dever??o ser implementados em
\Haskell.  H?? ainda um outro objectivo: o de ensinar a documentar
programas, a valid??-los e a produzir textos t??cnico-cient??ficos de
qualidade.

\section{Documenta????o} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma t??cnica de programa\-????o dita
``\litp{liter??ria}'' \cite{Kn92}, cujo princ??pio base ?? o seguinte:
%
\begin{quote}\em Um programa e a sua documenta????o devem coincidir.
\end{quote}
%
Por outras palavras, o c??digo fonte e a documenta????o de um
programa dever??o estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que est?? a ler ?? j?? um exemplo de
\litp{programa????o liter??ria}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrar?? no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} ??
um pre-processador que faz ``pretty printing''
de c??digo Haskell em \Latex\ e que deve desde j?? instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} ?? execut??vel e cont??m
o ``kit'' b??sico, escrito em \Haskell, para realizar o trabalho. Basta executar
\begin{Verbatim}[fontsize=\small]
    $ ghci cp2021t.lhs
\end{Verbatim}

%if False
\begin{code}
{-# OPTIONS_GHC -XNPlusKPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, DeriveDataTypeable, FlexibleInstances #-}
module Main where 
import Cp
import List hiding (fac)
import Nat
import LTree
import Data.List hiding (find)
import Test.QuickCheck hiding ((><),choose,collect)
import qualified Test.QuickCheck as QuickCheck
import Graphics.Gloss
import Graphics.Gloss.Interface.Pure.Game
import Control.Monad
import Control.Applicative hiding ((<|>))
import System.Process
\end{code}
%endif

\noindent Abra o ficheiro \texttt{cp2021t.lhs} no seu editor de texto preferido
e verifique que assim ??: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
?? seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho te??rico-pr??tico deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avalia????o (datas para submiss??o do relat??rio e sua defesa
oral) s??o os que forem publicados na \cp{p??gina da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder ??s quest??es que ser??o colocadas
na \emph{defesa oral} do relat??rio.

Em que consiste, ent??o, o \emph{relat??rio} a que se refere o par??grafo anterior?
?? a edi????o do texto que est?? a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relat??rio dever?? conter ainda a identifica????o dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relat??rio deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o ??ndice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-?? ainda instalar o utilit??rio
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
gera????o de gr??ficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invoc??-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o n??mero de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) c??digo
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
c??digo \Haskell\ relativo aos problemas que se seguem. Esse anexo dever??
ser consultado e analisado ?? medida que isso for necess??rio.

\subsection{Stack}

O \stack{Stack} ?? um programa ??til para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito espec??fica:

\begin{itemize}
\item Os m??dulos auxiliares encontram-se na pasta \emph{src}.
\item O m??dulos principal encontra-se na pasta \emph{app}.
\item A lista de dep??ndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as dep??ndencias externas ser??o instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados alg??bricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Gra??as ?? sua flexibilidade,
torna-se trivial implementar \DSL s
e at?? mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programa????o}.

Paralelamente, um t??pico bastante estudado no ??mbito de \DL\ 
?? a deriva????o autom??tica de express??es matem??ticas, por exemplo, de derivadas.
Duas t??cnicas que podem ser utilizadas para o c??lculo de derivadas s??o:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplica????o sucessiva de transforma????es
(leia-se: fun????es) que sejam congruentes com as regras de deriva????o. O resultado
final ser?? a express??o da derivada.

O leitor atento poder?? notar um problema desta t??cnica: a express??o
inicial pode crescer de forma descontrolada, levando a um c??lculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da express??o em todos os passos.
Para tal, ?? necess??rio calcular o valor da express??o \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de express??es matem??ticas simples e
implementar as duas t??cnicas de deriva????o autom??tica.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam opera????es bin??rias e un??rias, respectivamente:

\begin{code}
data BinOp = Sum
           | Product
           deriving (Eq, Show)

data UnOp = Negate
          | E
          deriving (Eq, Show)
\end{code}

\noindent
O construtor |E| simboliza o exponencial de base $e$.

Assim, cada express??o pode ser uma vari??vel, um n??mero, uma opera????o bin??ria
aplicada ??s devidas express??es, ou uma opera????o un??ria aplicada a uma express??o.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na nota????o matem??tica habitual.

\begin{enumerate}
\item A defini????o das fun????es |inExpAr| e |baseExpAr| para este tipo ?? a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as fun????es |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| s??o testemunhas de um isomorfismo,
    isto ??,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma express??o aritm??tica e um escalar para substituir o |X|,
	a fun????o

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da express??o. Na p??gina \pageref{pg:P1}
    esta fun????o est?? expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A fun????o |eval_exp| respeita os elementos neutros das opera????es.
\begin{code}
prop_sum_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idr a exp = eval_exp a exp .=?=. sum_idr where
  sum_idr = eval_exp a (Bin Sum exp (N 0))

prop_sum_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_sum_idl a exp = eval_exp a exp .=?=. sum_idl where
  sum_idl = eval_exp a (Bin Sum (N 0) exp)

prop_product_idr :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idr a exp = eval_exp a exp .=?=. prod_idr where
  prod_idr = eval_exp a (Bin Product exp (N 1))

prop_product_idl :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_product_idl a exp = eval_exp a exp .=?=. prod_idl where
  prod_idl = eval_exp a (Bin Product (N 1) exp)

prop_e_id :: (Floating a, Real a) => a -> Bool
prop_e_id a = eval_exp a (Un E (N 1)) == expd 1

prop_negate_id :: (Floating a, Real a) => a -> Bool
prop_negate_id a = eval_exp a (Un Negate (N 0)) == 0
\end{code}
    \end{propriedade}
    \begin{propriedade}
      Negar duas vezes uma express??o tem o mesmo valor que n??o fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item ?? poss??vel otimizar o c??lculo do valor de uma express??o aritm??tica tirando proveito
  dos elementos absorventes de cada opera????o. Implemente os genes da fun????o
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na p??gina \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual ?? a vantagem de implementar a fun????o |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A fun????o |optimize_eval| respeita a sem??ntica da fun????o |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma express??o, ?? necess??rio aplicar transforma????es
?? express??o original que respeitem as regras das derivadas:\footnote{%
	Apesar da adi????o e multiplica????o gozarem da propriedade comutativa,
	h?? que ter em aten????o a ordem das opera????es por causa dos testes.}

\begin{itemize}
  \item Regra da soma:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
  \item Regra do produto:
\begin{eqnarray*}
	\frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma express??o aritm??tica, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A fun????o |sd| respeita as regras de deriva????o.
\begin{code}
prop_const_rule :: (Real a, Floating a) => a -> Bool
prop_const_rule a = sd (N a) == N 0

prop_var_rule :: Bool
prop_var_rule = sd X == N 1

prop_sum_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_sum_rule exp1 exp2 = sd (Bin Sum exp1 exp2) == sum_rule where
  sum_rule = Bin Sum (sd exp1) (sd exp2)

prop_product_rule :: (Real a, Floating a) => ExpAr a -> ExpAr a -> Bool
prop_product_rule exp1 exp2 = sd (Bin Product exp1 exp2) == prod_rule where
  prod_rule =Bin Sum (Bin Product exp1 (sd exp2)) (Bin Product (sd exp1) exp2)

prop_e_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_e_rule exp = sd (Un E exp) == Bin Product (Un E exp) (sd exp)

prop_negate_rule :: (Real a, Floating a) => ExpAr a -> Bool
prop_negate_rule exp = sd (Un Negate exp) == Un Negate (sd exp)
\end{code}
    \end{propriedade}

\item Como foi visto, \emph{Symbolic differentiation} n??o ?? a t??cnica
mais eficaz para o c??lculo do valor da derivada de uma express??o.
\emph{Automatic differentiation} resolve este problema c??lculando o valor
da derivada em vez de manipular a express??o original.

  Defina o gene do catamorfismo que ocorre na fun????o
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma express??o aritm??tica e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a express??o original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| ?? equivalente a calcular a derivada da express??o e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programa????o din??mica} por c??lculo,
recorrendo ?? lei de recursividade m??tua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, p??gina \pageref{eq:fokkinga}.}

Para o caso de fun????es sobre os n??meros naturais (|Nat0|, com functor |fF
X = 1 + X|) ?? f??cil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que n??o tenham estudado
\cp{C??lculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
c??lculo do ciclo-\textsf{for} que implementa a fun????o de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-?? de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| ter?? tantos argumentos quanto o n??mero de fun????es mutuamente recursivas.
\item	Para as vari??veis escolhem-se os pr??prios nomes das fun????es, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros s??mbolos, mas numa primeira leitura
d?? jeito usarem-se tais nomes.}
\item	Para os resultados v??o-se buscar as express??es respectivas, retirando a vari??vel |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das fun????es, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polin??mios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o m??todo estudado nas aulas\footnote{Sec????o 3.17 de \cite{Ol18} e t??pico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade m??tua} nos v??deos das aulas te??ricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas fun????es mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementa????o, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}
O que se pede ent??o, nesta pergunta?
Dada a f??rmula que d?? o |n|-??simo \catalan{n??mero de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementa????o de $C_n$ que n??o calcule factoriais nenhuns.
Isto ??, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta fun????o.

\begin{propriedade}
A fun????o proposta coincidem com a defini????o dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugest??o}: Come??ar por estudar muito bem o processo de c??lculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da fun????o exponencial.


\Problema 

As \bezier{curvas de B??zier}, designa????o dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre B??zier},
s??o curvas ub??quas na ??rea de computa????o gr??fica, anima????o e modela????o.
Uma curva de B??zier ?? uma curva param??trica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ ?? a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de B??zier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} ?? um m??todo recursivo capaz de calcular
curvas de B??zier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo ?? numericamente mais est??vel, trocando velocidade por corre????o.

De forma sucinta, o valor de uma curva de B??zier de um s?? ponto $\{P_0\}$
(ordem $0$) ?? o pr??prio ponto $P_0$. O valor de uma curva de B??zier de ordem
$N$ ?? calculado atrav??s da interpola????o linear da curva de B??zier dos primeiros
$N-1$ pontos e da curva de B??zier dos ??ltimos $N-1$ pontos.

A interpola????o linear entre 2 n??meros, no intervalo $[0, 1]$, ?? dada pela
seguinte fun????o:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpola????o linear entre 2 pontos de dimens??o $N$ ?? calculada atrav??s
da interpola????o linear de cada dimens??o.

O tipo de dados |NPoint| representa um ponto com $N$ dimens??es.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimens??es e um ponto de 3 dimens??es podem ser
representados, respetivamente, por:
\begin{spec}
p2d = [1.2, 3.4]
p3d = [0.2, 10.3, 2.4]
\end{spec}
%
O tipo de dados |OverTime a| representa um termo do tipo |a| num dado instante
(dado por um |Float|).
\begin{code}
type OverTime a = Float -> a
\end{code}
%
O anexo \ref{sec:codigo} tem definida a fun????o 
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpola????o linear entre 2 pontos, e a fun????o
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua defini????o com a propriedade:
    \begin{propriedade} Defini????o alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a fun????o |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de B??zier s??o sim??tricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a fun????o |runBezier| e aprecie o seu trabalho\footnote{%
        A representa????o em Gloss ?? uma adapta????o de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que ?? aberta (que cont??m, a verde, um ponto
        inicila) com o bot??o esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a f??rmula que calcula a m??dia de uma lista n??o vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto ??, para sabermos a m??dia de uma lista precisamos de dois catamorfismos: o que faz o somat??rio e o que calcula o comprimento a lista.
Contudo, ?? facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ est?? em recursividade m??tua com $length$ e o par de fun????es pode ser expresso por um ??nico catamorfismo, significando que a lista apenas ?? percorrida uma vez.

\begin{enumerate}

\item	Recorra ?? lei de recursividade m??tua para derivar a fun????o
|avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length| em listas n??o vazias. 

\item	Generalize o racioc??nio anterior para o c??lculo da m??dia de todos os elementos de uma \LTree\ recorrendo a uma ??nica travessia da ??rvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas fun????es testando a propriedade seguinte:
\begin{propriedade}
A m??dia de uma lista n??o vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 mil??simas:
\begin{code}
prop_avg :: [Double] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta quest??o ?? \textbf{opcional} e funciona como \textbf{valoriza????o} apenas para os alunos que desejarem faz??-la.) 

\vskip 1em \noindent
Existem muitas linguagens funcionais para al??m do \Haskell, que ?? a linguagem usada neste trabalho pr??tico. Uma delas ?? o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os m??dulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede ?? a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execu????o: o c??digo que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para al??m disso, os grupos podem demonstrar o c??digo na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir c??lculos e diagramas em LaTeX/lhs2tex}
Como primeiro exemplo, estudar o texto fonte deste trabalho para obter o
efeito:\footnote{Exemplos tirados de \cite{Ol18}.} 
\begin{eqnarray*}
\start
	|id = split f g|
%
\just\equiv{ universal property }
%
        |lcbr(
		p1 . id = f
	)(
		p2 . id = g
	)|
%
\just\equiv{ identity }
%
        |lcbr(
		p1 = f
	)(
		p2 = g
	)|
\qed
\end{eqnarray*}

Os diagramas podem ser produzidos recorrendo ?? \emph{package} \LaTeX\ 
\href{https://ctan.org/pkg/xymatrix}{xymatrix}, por exemplo: 
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Nat0|
           \ar[d]_-{|cataNat g|}
&
    |1 + Nat0|
           \ar[d]^{|id + (cataNat g)|}
           \ar[l]_-{|inNat|}
\\
     |B|
&
     |1 + B|
           \ar[l]^-{|g|}
}
\end{eqnarray*}

\section{Programa????o din??mica por recursividade m??ltipla}\label{sec:recmul}
Neste anexo d??o-se os detalhes da resolu????o do Exerc??cio \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, p??gina \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o c??lculo da aproxima????o at?? |i=n| da fun????o exponencial $exp\ x = e^x$,
via s??rie de Taylor:
\begin{eqnarray}
	exp\ x 
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a fun????o que d?? essa aproxima????o.
?? f??cil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
m??tua. Se repetirmos o processo para |h x n| etc obteremos no total tr??s fun????es nessa mesma
situa????o:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na p??gina \ref{pg:regra} deste enunciado,
ter-se-??, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{C??digo fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Defini????o da s??rie de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Or??culo para inspec????o dos primeiros 26 n??meros de Catalan\footnote{Fonte:
\catalan{Wikipedia}.}:
\begin{code}
oracle = [
    1, 1, 2, 5, 14, 42, 132, 429, 1430, 4862, 16796, 58786, 208012, 742900, 2674440, 9694845,
    35357670, 129644790, 477638700, 1767263190, 6564120420, 24466267020,
    91482563640, 343059613650, 1289904147324, 4861946401452
    ]
\end{code}

\subsection*{Problema 3}
Algoritmo:
\begin{spec}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau [] = nil
deCasteljau [p] = const p
deCasteljau l = \pt -> (calcLine (p pt) (q pt)) pt where
  p = deCasteljau (init l)
  q = deCasteljau (tail l)
\end{spec}
Fun????o auxiliar:
\begin{spec}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine [] = const nil
calcLine(p:x) = curry g p (calcLine x) where
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{spec}
2D:
\begin{code}
bezier2d :: [NPoint] -> OverTime (Float, Float)
bezier2d [] = const (0, 0)
bezier2d l = \z -> (fromRational >< fromRational) . (\[x, y] -> (x, y)) $ ((deCasteljau l) z)
\end{code}
Modelo:
\begin{code}
data World = World { points :: [NPoint]
                   , time :: Float
                   }
initW :: World
initW = World [] 0

tick :: Float -> World -> World
tick dt world = world { time=(time world) + dt }

actions :: Event -> World -> World
actions (EventKey (MouseButton LeftButton) Down _ p) world =
  world {points=(points world) ++ [(\(x, y) -> map toRational [x, y]) p]}
actions (EventKey (SpecialKey KeyDelete) Down _ _) world =
    world {points = cond (== []) id init (points world)}
actions _ world = world

scaleTime :: World -> Float
scaleTime w = (1 + cos (time w)) / 2

bezier2dAtTime :: World -> (Float, Float)
bezier2dAtTime w = (bezier2dAt w) (scaleTime w)

bezier2dAt :: World -> OverTime (Float, Float)
bezier2dAt w = bezier2d (points w)

thicCirc :: Picture
thicCirc = ThickCircle 4 10

ps :: [Float]
ps = map fromRational ps' where
  ps' :: [Rational]
  ps' = [0, 0.01..1] -- interval
\end{code}
Gloss:
\begin{code}
picture :: World -> Picture
picture world = Pictures
  [ animateBezier (scaleTime world) (points world)
  , Color white . Line . map (bezier2dAt world) $ ps
  , Color blue . Pictures $ [Translate (fromRational x) (fromRational y) thicCirc | [x, y] <- points world]
  , Color green $ Translate cx cy thicCirc
  ] where
  (cx, cy) = bezier2dAtTime world
\end{code}
Anima????o:
\begin{code}
animateBezier :: Float -> [NPoint] -> Picture
animateBezier _ [] = Blank
animateBezier _ [_] = Blank
animateBezier t l = Pictures
  [ animateBezier t (init l)
  , animateBezier t (tail l)
  , Color red . Line $ [a, b]
  , Color orange $ Translate ax ay thicCirc
  , Color orange $ Translate bx by thicCirc
  ] where
  a@(ax, ay) = bezier2d (init l) t
  b@(bx, by) = bezier2d (tail l) t
\end{code}
Propriedades e \emph{main}:
\begin{code}
runBezier :: IO ()
runBezier = play (InWindow "B??zier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compila????o e execu????o dentro do interpretador:\footnote{Pode ser ??til em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma fun????o
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
C??digo para gera????o de testes:
\begin{code}
instance Arbitrary UnOp where
  arbitrary = elements [Negate, E]

instance Arbitrary BinOp where
  arbitrary = elements [Sum, Product]

instance (Arbitrary a) => Arbitrary (ExpAr a) where
  arbitrary = do
    binop <- arbitrary
    unop  <- arbitrary
    exp1  <- arbitrary
    exp2  <- arbitrary
    a     <- arbitrary

    frequency . map (id >< pure) $ [(20, X), (15, N a), (35, Bin binop exp1 exp2), (30, Un unop exp1)]


infixr 5 .=?=.
(.=?=.) :: Real a => a -> a -> Bool
(.=?=.) x y = (toRational x) == (toRational y)


\end{code}

\subsection*{Outras fun????es auxiliares}
%----------------- Outras defini????es auxiliares -------------------------------------------%
L??gicas:
\begin{code}
infixr 0 .==>.
(.==>.) :: (Testable prop) => (a -> Bool) -> (a -> prop) -> a -> Property
p .==>. f = \a -> p a ==> f a

infixr 0 .<==>.
(.<==>.) :: (a -> Bool) -> (a -> Bool) -> a -> Property
p .<==>. f = \a -> (p a ==> property (f a)) .&&. (f a ==> property (p a))

infixr 4 .==.
(.==.) :: Eq b => (a -> b) -> (a -> b) -> (a -> Bool)
f .==. g = \a -> f a == g a

infixr 4 .<=.
(.<=.) :: Ord b => (a -> b) -> (a -> b) -> (a -> Bool)
f .<=. g = \a -> f a <= g a

infixr 4 .&&&.
(.&&&.) :: (a -> Bool) -> (a -> Bool) -> (a -> Bool)
f .&&&. g = \a -> ((f a) && (g a))
\end{code}

%----------------- Solu????es dos alunos -----------------------------------------%

\section{Solu????es dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas solu????es para os exerc??cios
propostos, de acordo com o "layout" que se fornece. N??o podem ser
alterados os nomes ou tipos das fun????es dadas, mas pode ser adicionado
texto, disgramas e/ou outras fun????es auxiliares que sejam necess??rias.

Valoriza-se a escrita de \emph{pouco} c??digo que corresponda a solu????es
simples e elegantes. 

\subsection*{Problema 1} \label{pg:P1}
S??o dadas:
\begin{code}
cataExpAr g = g . recExpAr (cataExpAr g) . outExpAr
anaExpAr g = inExpAr . recExpAr (anaExpAr g) . g
hyloExpAr h g = cataExpAr h . anaExpAr g

eval_exp :: Floating a => a -> (ExpAr a) -> a
eval_exp a = cataExpAr (g_eval_exp a)

optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
optmize_eval a = hyloExpAr (gopt a) clean

sd :: Floating a => ExpAr a -> ExpAr a
sd = p2 . cataExpAr sd_gen

ad :: Floating a => a -> ExpAr a -> a
ad v = p2 . cataExpAr (ad_gen v)
\end{code}
\subsection{Solu????o: }
Uma vez que estamos a trabalhar com um tipo indutivo novo iremos representar o diagrama gen??rico de um catamorfismo que atua sobre o tipo indutivo ExprAr. Al??m disso, iremos representar o bifunctor de base bem como a fun????o out associada a este tipo indutivo.

Pela an??lise da fun????o |baseExprAr| conseguimos perceber de um modo geral como o bifunctor de base atua. 
Assim temos o seguinte diagrama:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
           \ar[d]_-{|cataExpAr f|}
&
    |1 + A + (BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)|
           \ar[d]^{|id + id + (id >< (cataExpAr f) + (cataExpAr f)) + (id >< (cataExpAr f))|}
           \ar[l]_-{|inExpAr|}
\\
     |A|
&
     |1 + A + (BinOp >< (A >< A)) + (UnOp >< A)|
           \ar[l]^-{|gene|}
}
\end{eqnarray*}

Como em qualquer catamorfismo, est?? presente o isomorfismo in- out e pelas leis de C??lculo de Programas, conseguimos obter a defini????o da fun????o outExpAr.

\textbf{NB}: Por efeitos de simplifica????o, iremos referir a fun????o |outExpAr| como apenas |out|.

Temos:

\begin{eqnarray*}
\start
  |out . inExpAr = id|
%
\just\equiv{ Defini????o de |inExpAr| }
%
|out . (either (const X) num_ops) = id|
%
\just\equiv{ Defini????o de |num_ops| }
%
|out . (either (const X) (either N ops))|
%
\just\equiv{ Defini????o de |ops| }
%
|out . (either (const X) (either N (either bin (uncurry Un))))|
%
\just\equiv{ Fus??o + (20) }
%
|either (out . (const X)) (either (out . N) (either (out . bin) (out . (uncurry Un)))) = id|
%
\just\equiv{ Universal + (17), Natural id (1) }
%
      \begin{lcbr}
          |out . (const X) = i1()|\\
          |either (out . N) (either (out . bin) (out . (uncurry Un))) = i2()|\\
      \end{lcbr}
%
\just\equiv{ Universal + (17) }
  %
      \begin{lcbr}
          |out . (const X) = i1()|\\
          \begin{lcbr}
              |out . N = i2() . i1()|\\
              |either (out . bin) (out . (uncurry Un) = i2() . i2()|\\
          \end{lcbr}
      \end{lcbr}
  %
\just\equiv{ Universal + (17) }
  %
      \begin{lcbr}
          |out . (const X) = i1()|\\
          \begin{lcbr}
              |out . N = i2() . i1()|\\
              \begin{lcbr}
                |out . bin = i2() . i2() . i1()|\\
                |out . (uncurry Un) = i2() . i2() . i2()|\\
              \end{lcbr}
          \end{lcbr}
      \end{lcbr}
  %
\just\equiv{ Ig Existencial (71), Def de Composi????o (72), Def de Const (74), Def de Uncurry (84), Def de |Un|, Def |Bin|}
  %
      \begin{lcbr}
          |out (X) = i1()|\\
          \begin{lcbr}
              |out (N x) = i2(i1( x))|\\
              \begin{lcbr}
                |out (Bin op a b) = i2(i2(i1(op , (a , b))))|\\
                |out (Un op a) = i2(i2(i2(op , a)))|\\
              \end{lcbr}
          \end{lcbr}
      \end{lcbr}
  %  
\qed
\end{eqnarray*}



\begin{code}
outExpAr (X) = i1()
outExpAr (N x) = i2(i1 x)
outExpAr (Bin op a b) = i2(i2(i1(op, (a, b))))
outExpAr (Un op a) = i2(i2(i2(op, a))) 
\end{code}
\subsection{Solu????o: }
Pela an??lise do diagrama, percebemos como a recursividade, isto ??, como um catamorfismo associado a este tipo indutivo "consome" a estrutura de dados. Temos tamb??m o functor do tipo indutivo dado pela fun????o |baseExpAr|.

Assim conseguimos chegar de forma indutiva ?? defini????o da fun????o recExpAr:
\begin{code}
recExpAr f= baseExpAr id id id f f id f
\end{code}
\subsection{Solu????o: }
Dada a situa????o em que nos ?? dado um escalar e uma express??o, ao termos de calcular o valor da mesma, substituindo o valor do escalar de forma apropriada ?? express??o, conseguimos mais uma vez atrav??s da an??lise do diagrama perceber como a recursividade est?? expl??cita neste caso.
Primeiramente iremos definir o diagrama associado ao catamorfismo |eval_exp|:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |ExpAr A|
           \ar[d]_-{|eval_exp|}
&
    |1 + A + (BinOp >< (ExpAr A >< ExpAr A)) + (UnOp >< ExpAr A)|
           \ar[d]^{|id + id + (id >< (eval_exp) + (eval_exp)) + (id >< (eval_exp))|}
           \ar[l]_-{|inExpAr|}
\\
     |A|
&
     |1 + A + (BinOp >< (A >< A)) + (UnOp >< A)|
           \ar[l]^-{|g_eval_exp|}
}
\end{eqnarray*}

?? de salientar que o ponto fulcral do problema ?? induzir o gene do catamorfismo |eval_exp|, ou seja "descobrir" como definir a fun????o |g_eval_exp|.
Ora consoante o tipo de |ExpAr| em  causa e um escalar, de forma a calcular o valor da express??o para esse escalar, temos uma das seguintes possibilidades ou at?? mesmo v??rias das seguintes possibilidades:

\begin{itemize}
  \item Caso 1: Uma express??o ser uma inc??gnita |x| e dado um escalar, o valor da express??o ?? o pr??prio escalar;
\end{itemize}
\begin{code}
g_eval_exp escalar (Left ()) = escalar
\end{code}
\begin{itemize}
  \item Caso 2: Uma express??o ser um escalar |valor| e dado um escalar, o valor da express??o ?? o pr??prio |valor|;
\end{itemize}
\begin{code}
g_eval_exp escalar (Right (Left valor)) = valor
\end{code}
\begin{itemize}
  \item Caso 3: Uma express??o ser uma soma/produto entre dois |ExpAr| e dado um escalar, o valor da express??o ?? somar/multiplicar os dois |ExpAr|, substituindo as inc??gnitas pelo escalar;
\end{itemize}
\textbf{NB}: ?? de salientar que ambos os |ExpAr| supramencionados foram j?? processados pelo catamorfismo e as inc??gnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code} 
g_eval_exp escalar (Right(Right(Left (Sum,(a,b))))) = a + b
g_eval_exp escalar (Right(Right(Left (Product,(a,b))))) = a * b
\end{code}
\begin{itemize}
  \item Caso 4: Uma express??o ser uma nega????o de um |ExpAr| e dado um escalar, o valor da express??o ?? negar o |ExpAr|, substituindo as inc??gnitas pelo escalar;
\end{itemize}
\textbf{NB}: ?? de salientar que o |ExpAr| supramencionado foi j?? processado pelo catamorfismo e as inc??gnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code}
g_eval_exp escalar (Right(Right(Right (Negate, a)))) = (-1) * a 
\end{code}
\begin{itemize}
  \item Caso 5: Uma express??o ser uma base de |e| cujo expoente ?? um |ExpAr| e dado um escalar, o valor da express??o ?? elevar a base |e| ao expoente |ExpAr|, substituindo as inc??gnitas pelo escalar;
\end{itemize}
\textbf{NB}: ?? de salientar que o |ExpAr| supramencionado foi j?? processado pelo catamorfismo e as inc??gnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code}
g_eval_exp escalar (Right(Right(Right (E, a)))) = Prelude.exp a
\end{code}

\subsection{Solu????o: }
De forma a tirar proveito das propriedades dos elementos absorventes e neutros das opera????es matem??ticas impostas no tipo indutivo em causa, teremos de analisar os v??rios casos em que conseguimos "limpar" uma express??o. Al??m disso, a maneira que iremos trabalhar com estes casos ?? a mesma para a fun????o |outExpAr| associada a este tipo indutivo, uma vez que iremos apenas receber uma |ExpAr| e a iremos "limpar".
Assim, consoante o tipo |ExpAr| em causa, de forma a tirar proveito das propriedades dos elementos neutro e absorventes temos uma das seguintes possibilidades ou at?? mesmo v??rias das seguintes possibilidades:
\begin{itemize}
  \item Caso 1: Uma express??o ser um produto de uma |ExpAr| com 0 ?? o mesmo que apenas ter 0, tirando proveito da propriedade do elemento absorvente da multiplica????o;
\end{itemize}
\begin{code}
clean (Bin Product a (N 0)) = outExpAr (N 0)
clean (Bin Product (N 0) a) = outExpAr (N 0)
\end{code}
\begin{itemize}
  \item Caso 2: Uma express??o ser a base de |e| cujo expoente ?? 0 ?? o mesmo que apenas ter 1, tirando proveito da propriedade do elemento absorvente da exponecia????o;
\end{itemize}
\begin{code}
clean (Un E (N 0)) = outExpAr (N 1)
\end{code}
\begin{itemize}
  \item Caso 3: Uma express??o ser a nega????o de 0 ?? o mesmo que apenas ter 0, tirando proveito da propriedade do elemento neutro da nega????o;
\end{itemize}
\begin{code}
clean (Un Negate (N 0)) = outExpAr (N 0)
\end{code}
\begin{itemize}
  \item Caso 4: Uma express??o que ?? partida n??o tira proveito de nenhuma das propriedades supramencionadas, ter?? de ser analisada nas suas partes, sendo esta an??lise j?? efetuada aquando da recursividade;
\end{itemize}
\emph{Caso 5}: Uma express??o que ?? partida n??o tira proveito de nenhuma das propriedades supramencionadas, ter?? de ser analisada nas suas partes, sendo esta an??lise j?? efetuada aquando da recursividade;
\begin{code}
clean x = outExpAr x
\end{code}

A fun????o gopt "consome", isto ??, calcula apenas a express??o, fazendo uso da fun????o |g_eval_exp| acima definida.
\begin{code}
gopt exp = g_eval_exp exp 
\end{code}
Ora ?? de ressalvar, que pela a an??lise da defini????o do hilomorfismo associado a este tipo indutivo, |hyloExpAr|, vemos que a fun????o que "constroi" a estrutura de dados, que desempenha o papel de anamorfismo, ?? a fun????o |clean| e a fun????o que consome esta estrutura interm??dia criada pela fun????o |clean| ?? a fun????o |gopt| que desempenha o papel de catamorfismo.

\subsection{Solu????o: }
Uma vez que queremos calcular a derivada de uma express??o, teremos de ter em conta os v??rios casos poss??veis e que se adequam ao tipo indutivo em causa e que est??o presentes na matem??tica que aprendemos no ensino b??sico. Al??m disso, pelas regras que nos s??o apresentadas como ponto de partida, conseguimos perceber que iremos lidar com um catamorfismo, que ter?? casos de base e casos recursivos, sendo que estes ??ltimos j?? ser??o processados pelo pr??prio catamorfismo |sd|. 
Primeiramente iremos analisar a tipagem da fun????o |sd_gen| que ir?? tratar do c??lculo da derivada de uma express??o do tipo |ExpAr|.
\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) -> (ExpAr a, ExpAr a)
\end{code}
Ao analisar a tipagem da fun????o |sd_gen| ficamos com uma d??vida: "O que s??o os pares de |ExpAr| nos operadores |Bin| e |Un|?".

Sabemos que estamos perante um gene de catamorfismo e que teremos casos em que, dado o operador em causa, temos argumentos por processar, isto ??, por calcular a sua derivada. Pela tipagem percebemos que o catamorfismo em causa pede os tais dois pares e pela a an??lise das regras de deriva????o, percebemos que a primeira componente de cada par ?? a express??o que ainda n??o foi derivada e a segunda componente ?? a express??o que j?? foi derivada.
Assim, consoante o tipo |ExpAr| em causa, seguindo as regras de deriva????o temos uma das seguintes possibilidades ou at?? mesmo v??rias das seguintes possibilidades:

\begin{itemize}
  \item Caso 1: Regra da derivada de uma inc??gnita:
\begin{eqnarray*}
  \frac{d}{dx}(x)= 1
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Left ()) = (X, N 1)
\end{code}
\begin{itemize}
  \item Caso 2: Regra da derivada de uma constante:
\begin{eqnarray*}
  \frac{d}{dx}(n)= 0
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Right(Left a)) = (N a, N 0)
\end{code}
\begin{itemize}
  \item Caso 3: Regra da derivada de uma soma:
\begin{eqnarray*}
  \frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Right (Right(Left (Sum, ((a, b), (c, d)))))) = (Bin Sum a c, Bin Sum b d)
\end{code}
\begin{itemize}
  \item Caso 4: Regra da derivada de uma produto:
\begin{eqnarray*}
  \frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Right (Right(Left (Product, ((a, b), (c, d)))))) = (Bin Product a c,(Bin Sum (Bin Product a d) (Bin Product b c)))
\end{code}
\begin{itemize}
  \item Caso 5: Regra da derivada de uma nega????o:
\end{itemize}
\begin{code}
sd_gen (Right(Right(Right (Negate, (a, b))))) = (Un Negate a, Un Negate b)
\end{code}
\begin{itemize}
  \item Caso 6: Regra da derivada de uma express??o cuja base ?? |e|:
\begin{eqnarray*}
  \frac{d}{dx}{e^a}= {e^a}\cdot \frac{d}{dx}(a)
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Right(Right(Right (E, (a, b))))) = (Un E a, Bin Product (Un E a) b)
\end{code}

\subsection{Solu????o: }
Sabemos que estamos perante um gene de catamorfismo e que teremos casos em que, dado o operador em causa, temos argumentos por processar, isto ??, por calcular a sua derivada. Al??m disso, agora ?? nos dados um escalar de forma a calcularmos a derivada no ponto (escalar) dado, sem manipular ou transformar a express??o em causa. Assim, consoante o tipo |ExpAr| em causa, seguindo as regras de deriva????o temos uma das seguintes possibilidades ou at?? mesmo v??rias das seguintes possibilidades: 
\begin{itemize}
  \item Caso 1: Regra da derivada de uma inc??gnita:
\begin{eqnarray*}
  \frac{d}{dx}(x)= 1
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Left ()) = (x, 1)
\end{code}
\begin{itemize}
  \item Caso 2: Regra da derivada de uma constante:
\begin{eqnarray*}
  \frac{d}{dx}(n)= 0
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Right(Left a)) = (a, 0)
\end{code}
\begin{itemize}
  \item Caso 3: Regra da derivada de uma soma:
\begin{eqnarray*}
  \frac{d}{dx}(f(x)+g(x))=\frac{d}{dx}(f(x))+\frac{d}{dx}(g(x))
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Left (Sum, ((a, b), (c, d)))))) = (a + c, b + d)
\end{code}
\begin{itemize}
  \item Caso 4: Regra da derivada de uma produto:
\begin{eqnarray*}
  \frac{d}{dx}(f(x)g(x))=f(x)\cdot \frac{d}{dx}(g(x))+\frac{d}{dx}(f(x))\cdot g(x)
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Left (Product, ((a, b), (c, d)))))) = (a * c, (a * d) + (b * c))
\end{code}
\begin{itemize}
  \item Caso 5: Regra da derivada de uma nega????o:
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Right (Negate, (a, b))))) = (a * (-1), b * (-1))
\end{code}
\begin{itemize}
  \item Caso 6: Regra da derivada de uma express??o cuja base ?? |e|:
\begin{eqnarray*}
  \frac{d}{dx}{e^a}= {e^a}\cdot \frac{d}{dx}(a)
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Right (E, (a, b))))) = (Prelude.exp a, b * (Prelude.exp a))
\end{code}

\subsection*{Problema 2}
\subsection*{Solu????o:}
Uma vez que queremos derivar uma implementa????o da f??rmula de Catalan, (fun????o |Cn|) sem fatoriais, teremos de descobrir alguma "propriedade" da mesma. Ora a base desta "propriedade" j?? nos ?? que ?? a recursividade m??tua. Assim, teremos de chegar a uma f??rmula que expresse recursividade m??tua,tendo como ponto de partida a f??rmula que d?? o n-??simo n??mero de Catalan:
\begin{eqnarray*}
\start
|C n = (2n)!/((n+1)! >< (n!))|
%
\qed
\end{eqnarray*}

Ao analisarmos a f??rmula e ao estarmos a trabalhar nos |Nat0|, conseguimos inferir o caso base e o caso recursivo da f??rmula de Catalan.
Assim, temos o caso base e o caso recursivo abaixo representados respetivamente:
\begin{eqnarray*}
\start
\just\equiv{ Defini????o do caso base, Defini????o do caso recursivo (para n + 1)}
%
      \begin{lcbr}
          |C 0 = 0!/(1! >< 0!)|\\
          |C(n+1)= Cn >< (2n+2)!/ ((n+2)!(n+1)!)|\\
      \end{lcbr}
%
\just\equiv{ Simplifica????o do caso base, Propriedade do factorial (|x! = x >< (x - 1)!|) }
%
      \begin{lcbr}
          |C 0 = 1|\\
          |C(n+1)= ((2n+2) >< (2n+1) >< (2n)!)/((n+2) >< (n+1) >< (n!) >< (n+1)!)|\\
      \end{lcbr}
%
\just\equiv{ Propriedade do factorial (|x! = x >< (x - 1)!|) }
%
      \begin{lcbr}
          |C 0 = 1|\\
          |C(n+1)= ((2n+2) >< (2n+1) >< (2n)!)/((n+2) >< (n+1) >< n! >< (n+1)!)|\\
      \end{lcbr}
%
\just\equiv{ Defini????o de |C n = (2n)!/ ((n!) >< (n+1)!)| }
%
      \begin{lcbr}
          |C 0 =1|\\
          |C(n+1)= Cn >< ((2n+2) >< (2n+1))/((n+2) >< (n+1))|\\
      \end{lcbr}
%
\just\equiv{ Colocar o 2 em evid??ncia }
%
      \begin{lcbr}
          |C 0 = 1|\\
          |C(n+1)= Cn >< (2(n+1) >< (2n+1))/((n+2) >< (n+1))|\\
      \end{lcbr}
%
\just\equiv{ Cortar o denomidor e numerador |n+1| }
%
      \begin{lcbr}
          |C 0 =1|\\
          |C(n+1)= Cn ><  (2(2n+1))/(n+2)|\\
      \end{lcbr}
%
\just\equiv{ Intrudu????o das fun????es |f| e |g| }
%
      \begin{lcbr}
          |C 0 =1|\\
          |C(n+1)= Cn ><  f(n)/g(n)|\\
      \end{lcbr}
%
\qed
\end{eqnarray*}

\textbf{NB}: Criamos duas fun????es de forma a simplificar o c??lculo, em que a fun????o |f| ?? o numerador e a fun????o |g| ?? o denominador.
Tendo:

|f(n)= 2(2n+1)|

|g(n)= n+2|

Uma vez definidas as fun????es "auxiliares", conseguimos tamb??m definir os casos base das mesma. Tal como referido anteriormente, como estamos nos |Nat0|, conseguimos induzir facilmente os casos base das fun????es e ??l??m disso, simplificar as mesmas, tendo-se:
\begin{eqnarray*}
\start
\just\equiv{ Defini????o de |f|, Defini????o de |g| }
%
      \begin{lcbr}
          |f(n)= 2(2n+1)|\\
          |g(n)= n+2|\\
      \end{lcbr}
%
\just\equiv{ Defini????o do caso base e recursivo de |f|, Defini????o do caso base e recursivo de |g| }
%
      \begin{lcbr}
        \begin{lcbr}
          |f(0) = 2|\\
          |f(n+1)= 2(2(n+1)+1)|\\
          \end{lcbr}
          \begin{lcbr}
          |g(0) = 2|\\
          |g(n+1) = n+2+1|\\
          \end{lcbr}
      \end{lcbr}
%
\just\equiv{ Simplifica????o do caso recursivo de |f| }
%
      \begin{lcbr}
        \begin{lcbr}
          |f(0) = 2|\\
          |f(n+1)= 2(2n+1)+4|\\
          \end{lcbr}
          \begin{lcbr}
          |g(0) = 2|\\
          |g(n+1) = n+2+1|\\
          \end{lcbr}
      \end{lcbr}
%
\just\equiv{ Defini????o de |f n = 2(2n+1)|, Defini????o de |g n = n+2| }
%
      \begin{lcbr}
        \begin{lcbr}
          |f(0) = 2|\\
          |f(n+1)= f(n) + 4|\\
          \end{lcbr}
          \begin{lcbr}
          |g(0) = 2|\\
          |g(n+1) = g(n)+1|\\
          \end{lcbr}
      \end{lcbr}
%
\qed
\end{eqnarray*}
Ap??s a simplifica????o da f??rmula de Catalan dada, conseguimos chegar a uma express??o que n??o depende de factoriais. Ao analisar em detalhe, percebemos algo fulcral, que ?? a exist??ncia de recursividade m??tua nesta nova express??o.

Estamos prontos para usar a dica que nos foi dado no enunciado, usando a fun????o |loop|. Segundo o enunciado, na primeira etapa "O corpo do ciclo loop ter?? tantos argumentos quanto o n??mero de fun????es mutuamente recursivas.", ora as fun????es mutuamente recursivas ser??o 3 sendo que 2 delas formar??o um par (as fun????es |f| e |g|). Seguindo a segunda etapa "Para as vari??veis escolhem-se os pr??prios nomes das fun????es, pela ordem que se achar conveniente", sendo que os argumentos da fun????o |loop| ser??o as fun????es mutuamente recursivas |f|, |g| e |C|. Com estas etapas juntamente com a terceira etapa, temos a defini????o da fun????o |loop|:
\begin{eqnarray*}
\start
|loop (C,(f,g)) = ((C*f)/g ,(f+4, g+1))|
\qed
\end{eqnarray*}

\textbf{NB}: ?? de salientar que a fun????o |loop| ?? quem vai tratar da recursividade m??tua das v??rias fun????es em causa (|f|, |g|, |C|);

Ao chegarmos ?? etapa final, a fun????o init vai recolher os casos bases pela mesma ordem que as fun????es argumentos aparecem na fun????o |loop|. Assim e analisando os c??lculos acima, temos a defini????o da fun????o |init|: 
\begin{eqnarray*}
\start
|init = (1, 2, 2)|
\qed
\end{eqnarray*}

Baseando-nos no exemplo aplicamos tamb??m a fun????o |p1| ap??s o |for loop init|, obtendo:
\begin{eqnarray*}
\start
|cat = p1 . for loop init|
\qed
\end{eqnarray*}
Assim, obtemos as defini????es das fun????es supramencionadas:
\begin{code}
f 0 = 2
f (n + 1)= f(n) + 4

g 0 = 2
g (n + 1) = g(n) + 1

c 0 = 1
c (n + 1) = c(n) * (f(n)/ g(n))

loop (c,(f,g)) = (uncurry div ((c * f), g) ,( f + 4, g +  1))
inic = (1, (2, 2))
prj = p1
\end{code}
por forma a que
\begin{code}
cat = prj . (for loop inic)
\end{code}
seja a fun????o pretendida.
\textbf{NB}: usar divis??o inteira.
Apresentar de seguida a justifica????o da solu????o encontrada.
\subsection*{Problema 3}
\subsection{Solu????o: }
Uma vez que a fun????o |calcLine| calcula a interpola????o linear entre dois pontos e cada um destes pontos ?? do tipo |NPoint| que por sua vez ?? uma lista de |Rational| de tamanho |N|, sendo |N| o n??mero de dimens??es de cada ponto, temos que a fun????o |calcLine| ?? um catamorfismo tal ?? referido no enunciado, que ir?? "consumir" as dimens??es em causa. Dado que o tipo em causa "consome" listas de |Rational| conseguimos perceber e inferir que o bifunctor de base associado a este tipo indutivo ?? o mesmo que ?? usado para o tipo indutivo |List|. Assim temos:

  |T A = NPoint|

  |B(X, Y) = X + X >< Y|

  |B(id, f) = id + id >< f|

De seguida, iremos definir o diagrama gen??rico associado ao tipo indutivo |NPoint|:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Npoint|
           \ar[d]_-{|(cata f)|}
&
    |1 + Q * Npoint|
           \ar[d]^{|id + id >< (cata f)|}
           \ar[l]_-{|in|}
\\
     |(Npoint -> Overtime Npoint)|
&
     |1 + Q >< (Npoint -> Overtime Npoint)|
           \ar[l]^-{|gene|}
}
\end{eqnarray*}

Com a informa????o do diagrama acima, conseguimos inferir o diagrama associado ao catamorfismo |calcLine|:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |Npoint|
           \ar[d]_-{|calcLine|}
&
    |1 + Q * Npoint|
           \ar[d]^{|id + id >< calcLine|}
           \ar[l]_-{|in|}
\\
     |(Npoint -> Overtime Npoint)|
&
     |1 + Q >< (Npoint -> Overtime Npoint)|
           \ar[l]^-{|h|}
}
\end{eqnarray*}

Como foi referido anteriormente, uma vez que a fun????o |calcLine| ?? um catamorfismo, falta-nos induzir o gene |h| associado a este catamorfismo. Conseguimos perceber atrav??s da dica dada no anexo \ref{sec:codigo}, que o gene ir?? fazer uso da fun????o |g| disponibilizada para tratar do que vem da recursividade. Assim, conseguimos chegar ?? defini????o da fun????o |calcLine| atrav??s do seu gene.
Com isto tem-se: 
\begin{code}
calcLine :: NPoint -> (NPoint -> OverTime NPoint)
calcLine = cataList h where
   h =  either (const(const nil)) g
   g :: (Rational, NPoint -> OverTime NPoint) -> (NPoint -> OverTime NPoint)
   g (d,f) l = case l of
       []     -> nil
       (x:xs) -> \z -> concat $ (sequenceA [singl . linear1d d x, f xs]) z
\end{code}
\subsection{Solu????o: }
\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau = hyloAlgForm alg coalg where
   coalg = undefined
   alg = undefined

hyloAlgForm = undefined
\end{code}

\subsection*{Problema 4}

\subsection{ Solu????o para listas n??o vazias:}

Uma vez que estamos a trabalhar com listas n??o vazias teremos que definir um tipo indutivo para tal.Ora este ir?? ser muito semelhante ao j?? conhecido tipo indutivo List.
Assim temos: 

  |T A = NotEmptyList A|

  |B(X, Y) = X + X >< Y|

  |B(id, f) = id + id >< f|

Diagrama gen??rico de um catamorfismo sobre o tipo indutivo |NotEmptyList|:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NotEmptyList A|
           \ar[d]_-{|cataNotEmptyList f|}
&
    |A + A * NotEmptyList A|
           \ar[d]^{|id + id >< (cataNotEmptyList f)|}
           \ar[l]_-{|inNotEmptyList|}
\\
     |B|
&
     |A + A >< B|
           \ar[l]^-{|f|}
}
\end{eqnarray*}
Al??m disso, teremos de definir a fun????o out assim como a fun????o que caracteriza o comportamento recursivo de um catamorfismo sobre o tipo indutivo supramencionado. Deste modo temos:

\begin{code}

outNotEmptyList [a]    = i1 (a)
outNotEmptyList (a:x) = i2(a,x)

recNotEmptyList  f   = id -|- id >< f 

cataNotEmptyList g = g . recNotEmptyList (cataNotEmptyList g) . outNotEmptyList
\end{code}

 Uma vez que temos na al??nea 1 do enunciado do Problema: |avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length|
para listas n??o vazias, teremos primeiro de definir o gene da fun????o length e da fun????o avg para o tipo indutivo em causa. Assim temos, para a fun????o length: 

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NotEmptyList A|
           \ar[d]_-{length}
&
    |A + A >< NotEmptyList A|
           \ar[d]^{|id + id >< (length)|}
           \ar[l]_-{|inNotEmptyList|}
\\
     |A|
&
     |A + A >< A|
           \ar[l]^-{|either one (succ. p2)|}
}
\end{eqnarray*}

E para a a fun????o avg, temos:
\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NotEmptyList A|
           \ar[d]_-{avg}
&
    |A + A >< NotEmptyList A|
           \ar[d]^{|id + id >< (avg)|}
           \ar[l]_-{|inNotEmptyList|}
\\
     |A|
&
     |A + A >< A|
           \ar[l]^-{|either g1 g2|}
}
\end{eqnarray*}

Onde:

|g1 = id|

|g2 = uncurry div (uncurry add (p1,(uncurry mul (p2, k))), succ k)|

|k = length x|

Em que |x| ?? a cauda da lista.

\textbf{NB}: Para efeito de simplifica????o, usaremos o gene do catamorfismo avg como  |either g1 g2|.

Uma vez que queremos usar a lei de recursividade m??tua, temos como ponto de partida a seguinte express??o:

  |avg_aux = split avg length|

Onde o diagrama da fun????o |avg_aux| ?? o seguinte:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |NotEmptyList A|
           \ar[d]_-{|avg_aux|}
&
    |A + A >< NotEmptyList A|
           \ar[d]^{|id + (id >< |avg_aux|)|}
           \ar[l]_-{|inNotEmptyList|}
\\
     |A >< A|
&
     |A + (A >< (A >< A))|
           \ar[l]^-{|either b q|}
}
\end{eqnarray*}

Assim, teremos de aplicar as leis do C??lculo de Programas:
\begin{eqnarray*}
\start
|avg_aux = split avg length|
%
\just\equiv{ Defini????o de avg como catamorfismo, defini????o de length como catamorfismo }
%
|avg_aux = split (either g1 g2) (either one (succ.p2))|
%
\just\equiv{ Lei Banana-Split (53) }
%
|avg_aux = cata (((either g1 g2) >< (either one (succ.p2))) . split (F p1) (F p2)|
%
\just\equiv{ Defini????o de Functor para |NotEmptyList| }
%
|avg_aux = cata ((either g1 g2) >< (either one (succ . p2)) .  split (id + (id >< p1)) (id + (id >< p2)))|
%
\just\equiv{ Lei Absor????o x (11) }
%
|avg_aux = cata (split ((either g1 g2). (id + id >< p1)) ((either one (succ.p2)). (id + id >< p2)))|
%
\just\equiv{ Lei Absor????o + (22), Natural id (1), natural |p2| (13) }
%
|avg_aux = cata (split (either g1 (g2.(id >< p1))) (either one (succ.p2.p2)))|
%
\just\equiv{ Lei da Troca (28) }
%
|avg_aux = cata (either (split g1 one) (split (g2.(id >< p1)) (succ.p2.p2)))|
%
\qed
\end{eqnarray*}

\begin{code}
\end{code}
Desta forma cheg??mos ao pretendido:
|avg_aux = cata (either b q)|

Com

|b = split g1 one|

|q = split (g2.(id >< p1)) (succ.p2.p2)|

E substituindo pelas defini????es de g1 e g2, temos:

|b = split id one|

|q = split av len|

Onde:

|av = uncurry div (uncurry add (p1,(uncurry mul (p2, k))), succ k). (id >< p1)|

|len = succ.p2.p2|

Com isto, temos ent??o definida a fun????o |avg_aux| sobre a forma de um catamorfismo.

\begin{code} 
avg_aux = cataNotEmptyList gene where
  gene = either b q 
  b = split id (const 1)
  q = split av len
  av(valor, (med, comp)) = ((med* comp) + valor) / (comp+ 1)
  len(valor, (med, comp)) = comp + 1

\end{code}

\begin{code}
avg = p1.avg_aux
\end{code}

\subsection{ Solu????o para ??rvores de tipo \LTree: }

Ora, ap??s o racioc??nio para o tipo indutivo |NotEmptyList|, o racioc??nio para o tipo indutivo \LTree\ ?? o mesmo.

\textbf{NB}: A diferen??a ?? que para este tipo indutivo temos que a m??dia s?? ?? calculada nas folhas e temos de ir somando o comprimento das sub-??rvores (ramo da esquerda e ramo da direita).

Assim temos que a fun????o |avgLTree| ?? um split de catamorfismos. Logo, temos o seguinte diagrama:

\begin{eqnarray*}
\xymatrix@@C=2cm{
    |LTree A|
           \ar[d]_-{|avgLTree|}
&
    |A + LTree A >< LTree A|
           \ar[d]^{|id + (|avgLTree| >< |avgLTree|)|}
           \ar[l]_-{|in|}
\\
     |(A >< A)|
&
     |A + ((A >< A) >< (A >< A))|
           \ar[l]^-{|either b q|}
}
\end{eqnarray*}

Seguindo o mesmo racioc??nio, mas aplicado ao tipo indutivo \LTree\ temos agora dois pares obtidos atrav??s da recursividade m??tua das fun????es length e avg para este tipo indutivo. Assim cada par ?? constituido pela m??dia das folhas e comprimento das sub-??rvores.

\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either b q 
   b = split id (const 1)
   q = split av len
   av((med_l, comp_l), (med_r, comp_r)) = (med_l * comp_l + med_r *comp_r) / (comp_l + comp_r)
   len((med_l, comp_l), (med_r, comp_r)) = comp_l + comp_r


\end{code}

\subsection*{Problema 5}
Inserir em baixo o c??digo \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

\begin{verbatim}
// {-# OPTIONS_GHC -XNPlusKPatterns #-}

// (c) MP-I (1998/9-2006/7) and CP (2005/6-2016/7)

module BTree 

open Cp
//import Data.List
//import Data.Monoid

// (1) Datatype definition -----------------------------------------------------

type BTree<'a> = Empty | Node of 'a * (BTree<'a> * BTree<'a>)

let inBTree x = (either (konst Empty) Node) x

let outBTree x = 
      match x with
      | Empty -> Left ()
      | Node (a,(t1,t2)) -> Right (a,(t1,t2))

// (2) Ana + cata + hylo -------------------------------------------------------

// recBTree g = id -|- (id >< (g >< g))

let baseBTree f g = id -|- (f >< (g >< g))

let recBTree g = baseBTree id g

let rec cataBTree g x = (g << (recBTree (cataBTree g)) << outBTree) x

let rec anaBTree g x = (inBTree << (recBTree (anaBTree g)) << g) x

let hyloBTree h g x = (cataBTree h << anaBTree g) x



// (3) Map ---------------------------------------------------------------------

// instance Functor BTree
//       where fmap f = cataBTree ( inBTree . baseBTree f id )
let fmap f x = cataBTree ( inBTree << baseBTree f id ) x

// equivalent to:
//       where fmap f = anaBTree ( baseBTree f id . outBTree )

// (4) Examples ----------------------------------------------------------------

// (4.1) Inversion (mirror) ----------------------------------------------------

let invBTree x = cataBTree (inBTree << (id -|- (id >< swap))) x

// (4.2) Counting --------------------------------------------------------------

let countBTree x = cataBTree (either (konst 0) (succ << (uncurry (+)) << p2)) x

// (4.3) Serialization ---------------------------------------------------------

let preord x = 
    let f(x,(l,r))=x::l@r
    in (either nil f) x

let preordt x = cataBTree preord x  // pre-order traversal

let postordt x = 
    let f(x,(l,r))=l@r@[x]
    in cataBTree (either nil f) x   // post-order traversal

let inord x = 
    let join(x,(l,r))=l@[x]@r
     in (either nil join) x

let inordt x = cataBTree inord x   // in-order traversal

// (4.4) Quicksort -------------------------------------------------------------

let rec part r c = 
  match c with
  | [] -> ([],[])
  | (x::xs) -> let (s,c) = part r xs 
                in if x < r then (x::s,c) else (s,x::c)

let qsep l = 
  match l with
  | [] -> Left ()
  | (x::xs) -> let (s,l) = part x xs in Right (x,(s,l))

let qSort x = hyloBTree inord qsep x // the same as (cataBTree inord). (anaBTree qsep)

(* pointwise versions:
qSort [] = []
qSort (h:t) = let (t1,t2) = part (<h) t
              in  qSort t1 ++ [h] ++ qSort t2

or, using list comprehensions:

qSort [] = []
qSort (h:t) = qSort [ a | a <- t , a < h ] ++ [h] ++ 
              qSort [ a | a <- t , a >= h ]

*)
// (4.5) Traces ----------------------------------------------------------------

let auxAdd c t = c :: t

let rec union c1 c2 = 
     match c2 with
     | [] -> c1
     | (h::t) -> if (List.exists (fun c -> c = h) c1) then union c1 t
                                       else union (c1@[h]) t 

let tunion(a,(l,r)) = union (List.map (auxAdd a) l) (List.map (auxAdd a) r)

let traces x = cataBTree (either (konst [[]]) tunion) x


// (4.6) Towers of Hanoi -------------------------------------------------------

// pointwise:
// hanoi(d,0) = []
// hanoi(d,n+1) = (hanoi (not d,n)) ++ [(n,d)] ++ (hanoi (not d, n))


let present x = inord x  // same as in qSort

let strategy x = 
  match x with
  |(d,0) -> Left ()
  |(d,n) -> Right ((n-1,d),((not d,n-1),(not d,n-1)))

let hanoi x = hyloBTree present strategy x

(*
    The Towers of Hanoi problem comes from a puzzle marketed in 1883
    by the French mathematician ??douard Lucas, under the pseudonym
    Claus. The puzzle is based on a legend according to which
    there is a temple, apparently in Bramah rather than in Hanoi as
    one might expect, where there are three giant poles fixed in the
    ground. On the first of these poles, at the time of the world's
    creation, God placed sixty four golden disks, each of different
    size, in decreasing order of size. The Bramin monks were given
    the task of moving the disks, one per day, from one pole to another
    subject to the rule that no disk may ever be above a smaller disk.
    The monks' task would be complete when they had succeeded in moving
    all the disks from the first of the poles to the second and, on
    the day that they completed their task the world would come to
    an end!
    
    There is a well??known inductive solution to the problem given
    by the pseudocode below. In this solution we make use of the fact
    that the given problem is symmetrical with respect to all three
    poles. Thus it is undesirable to name the individual poles. Instead
    we visualize the poles as being arranged in a circle; the problem
    is to move the tower of disks from one pole to the next pole in
    a specified direction around the circle. The code defines H n d
    to be a sequence of pairs (k,d') where n is the number of disks,
    k is a disk number and d and d' are directions. Disks are numbered
    from 0 onwards, disk 0 being the smallest. (Assigning number 0
    to the smallest rather than the largest disk has the advantage
    that the number of the disk that is moved on any day is independent
    of the total number of disks to be moved.) Directions are boolean
    values, true representing a clockwise movement and false an anti??clockwise
    movement. The pair (k,d') means move the disk numbered k from
    its current position in the direction d'. The semicolon operator
    concatenates sequences together, [] denotes an empty sequence
    and [x] is a sequence with exactly one element x. Taking the pairs
    in order from left to right, the complete sequence H n d prescribes
    how to move the n smallest disks one??by??one from one pole to the
    next pole in the direction d following the rule of never placing
    a larger disk on top of a smaller disk.
    
    H 0     d = [],
    H (n+1) d = H n ??d ; [ (n, d) ] ; H n ??d.
    
    (excerpt from R. Backhouse, M. Fokkinga / Information Processing
    Letters 77 (2001) 71--76)
    
*)


// (5) Depth and balancing (using mutual recursion) --------------------------


let baldepth x = 
  let h(a,((b1,b2),(d1,d2))) = (b1 && b2 && abs(d1-d2)<=1,1+max d1 d2)
  let f((b1,d1),(b2,d2)) = ((b1,b2),(d1,d2))
  let g x = (either (konst(true,1)) (h<<(id><f))) x
  in cataBTree g x

let balBTree x = (p1 << baldepth) x

let depthBTree x = (p2 << baldepth) x

(*
// (6) Going polytipic -------------------------------------------------------

// natural transformation from base functor to monoid

let tnat f = let theta = uncurry mappend 
  in either (const mempty) (theta . (f >< theta))
  
// monoid reduction 

let monBTree f = cataBTree (tnat f)

// alternative to (4.2) serialization ----------------------------------------

let preordt' = monBTree singl

// alternative to (4.1) counting ---------------------------------------------

let countBTree' = monBTree (const (Sum 1))

// (7) Zipper ----------------------------------------------------------------

type Deriv <'a> = Dr Bool of 'a * BTree <'a>

type Zipper <'a> = [ Deriv <'a> ]

let rec plug l =
  match l with
  | [] t -> t
  | ((Dr False a l):z) t -> Node (a,(plug z t,l))
  | ((Dr True  a r):z) t -> Node (a,(r,plug z t))

---------------------------- end of library ----------------------------------
*)
\end{verbatim}

%----------------- Fim do anexo com solu????es dos alunos ------------------------%

%----------------- ??ndice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
