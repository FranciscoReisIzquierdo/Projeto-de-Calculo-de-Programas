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
       	Cálculo de Programas
\\
       	Trabalho Prático
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
a93273 & José Pedro Martins Magalhães
\\
a89526 & Duarte Augusto Rodrigues Lucas	
\\
a93185 & Carlos Filipe Almeida Dias
\end{tabular}
\end{center}

\section{Preâmbulo}

\CP\ tem como objectivo principal ensinar
a progra\-mação de computadores como uma disciplina científica. Para isso
parte-se de um repertório de \emph{combinadores} que formam uma álgebra da
programação (conjunto de leis universais e seus corolários) e usam-se esses
combinadores para construir programas \emph{composicionalmente}, isto é,
agregando programas já existentes.
  
Na sequência pedagógica dos planos de estudo dos dois cursos que têm
esta disciplina, opta-se pela aplicação deste método à programação
em \Haskell\ (sem prejuízo da sua aplicação a outras linguagens 
funcionais). Assim, o presente trabalho prático coloca os
alunos perante problemas concretos que deverão ser implementados em
\Haskell.  Há ainda um outro objectivo: o de ensinar a documentar
programas, a validá-los e a produzir textos técnico-científicos de
qualidade.

\section{Documentação} Para cumprir de forma integrada os objectivos
enunciados acima vamos recorrer a uma técnica de programa\-ção dita
``\litp{literária}'' \cite{Kn92}, cujo princípio base é o seguinte:
%
\begin{quote}\em Um programa e a sua documentação devem coincidir.
\end{quote}
%
Por outras palavras, o código fonte e a documentação de um
programa deverão estar no mesmo ficheiro.

O ficheiro \texttt{cp2021t.pdf} que está a ler é já um exemplo de
\litp{programação literária}: foi gerado a partir do texto fonte
\texttt{cp2021t.lhs}\footnote{O suffixo `lhs' quer dizer
\emph{\lhaskell{literate Haskell}}.} que encontrará no
\MaterialPedagogico\ desta disciplina descompactando o ficheiro
\texttt{cp2021t.zip} e executando:
\begin{Verbatim}[fontsize=\small]
    $ lhs2TeX cp2021t.lhs > cp2021t.tex
    $ pdflatex cp2021t
\end{Verbatim}
em que \href{https://hackage.haskell.org/package/lhs2tex}{\texttt\LhsToTeX} é
um pre-processador que faz ``pretty printing''
de código Haskell em \Latex\ e que deve desde já instalar executando
\begin{Verbatim}[fontsize=\small]
    $ cabal install lhs2tex --lib
\end{Verbatim}
Por outro lado, o mesmo ficheiro \texttt{cp2021t.lhs} é executável e contém
o ``kit'' básico, escrito em \Haskell, para realizar o trabalho. Basta executar
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
e verifique que assim é: todo o texto que se encontra dentro do ambiente
\begin{quote}\small\tt
\verb!\begin{code}!
\\ ... \\
\verb!\end{code}!
\end{quote}
é seleccionado pelo \GHCi\ para ser executado.

\section{Como realizar o trabalho}
Este trabalho teórico-prático deve ser realizado por grupos de 3 (ou 4) alunos.
Os detalhes da avaliação (datas para submissão do relatório e sua defesa
oral) são os que forem publicados na \cp{página da disciplina} na \emph{internet}.

Recomenda-se uma abordagem participativa dos membros do grupo
de trabalho por forma a poderem responder às questões que serão colocadas
na \emph{defesa oral} do relatório.

Em que consiste, então, o \emph{relatório} a que se refere o parágrafo anterior?
É a edição do texto que está a ser lido, preenchendo o anexo \ref{sec:resolucao}
com as respostas. O relatório deverá conter ainda a identificação dos membros
do grupo de trabalho, no local respectivo da folha de rosto.

Para gerar o PDF integral do relatório deve-se ainda correr os comando seguintes,
que actualizam a bibliografia (com \Bibtex) e o índice remissivo (com \Makeindex),
\begin{Verbatim}[fontsize=\small]
    $ bibtex cp2021t.aux
    $ makeindex cp2021t.idx
\end{Verbatim}
e recompilar o texto como acima se indicou. Dever-se-á ainda instalar o utilitário
\QuickCheck,
que ajuda a validar programas em \Haskell\ e a biblioteca \gloss{Gloss} para
geração de gráficos 2D:
\begin{Verbatim}[fontsize=\small]
    $ cabal install QuickCheck gloss --lib
\end{Verbatim}
Para testar uma propriedade \QuickCheck~|prop|, basta invocá-la com o comando:
\begin{verbatim}
    > quickCheck prop
    +++ OK, passed 100 tests.
\end{verbatim}
Pode-se ainda controlar o número de casos de teste e sua complexidade,
como o seguinte exemplo mostra:
\begin{verbatim}
    > quickCheckWith stdArgs { maxSuccess = 200, maxSize = 10 } prop
    +++ OK, passed 200 tests.
\end{verbatim}
Qualquer programador tem, na vida real, de ler e analisar (muito!) código
escrito por outros. No anexo \ref{sec:codigo} disponibiliza-se algum
código \Haskell\ relativo aos problemas que se seguem. Esse anexo deverá
ser consultado e analisado à medida que isso for necessário.

\subsection{Stack}

O \stack{Stack} é um programa útil para criar, gerir e manter projetos em \Haskell.
Um projeto criado com o Stack possui uma estrutura de pastas muito específica:

\begin{itemize}
\item Os módulos auxiliares encontram-se na pasta \emph{src}.
\item O módulos principal encontra-se na pasta \emph{app}.
\item A lista de depêndencias externas encontra-se no ficheiro \emph{package.yaml}.
\end{itemize}

Pode aceder ao \GHCi\ utilizando o comando:
\begin{verbatim}
stack ghci
\end{verbatim}

Garanta que se encontra na pasta mais externa \textbf{do projeto}.
A primeira vez que correr este comando as depêndencias externas serão instaladas automaticamente.

Para gerar o PDF, garanta que se encontra na diretoria \emph{app}.

\Problema

Os \emph{tipos de dados algébricos} estudados ao longo desta disciplina oferecem
uma grande capacidade expressiva ao programador. Graças à sua flexibilidade,
torna-se trivial implementar \DSL s
e até mesmo \href{http://www.cse.chalmers.se/~ulfn/papers/thesis.pdf}{linguagens de programação}.

Paralelamente, um tópico bastante estudado no âmbito de \DL\ 
é a derivação automática de expressões matemáticas, por exemplo, de derivadas.
Duas técnicas que podem ser utilizadas para o cálculo de derivadas são:

\begin{itemize}
\item \emph{Symbolic differentiation}
\item \emph{Automatic differentiation}
\end{itemize}

\emph{Symbolic differentiation} consiste na aplicação sucessiva de transformações
(leia-se: funções) que sejam congruentes com as regras de derivação. O resultado
final será a expressão da derivada.

O leitor atento poderá notar um problema desta técnica: a expressão
inicial pode crescer de forma descontrolada, levando a um cálculo pouco eficiente.
\emph{Automatic differentiation} tenta resolver este problema,
calculando \textbf{o valor} da derivada da expressão em todos os passos.
Para tal, é necessário calcular o valor da expressão \textbf{e} o valor da sua derivada.

Vamos de seguida definir uma linguagem de expressões matemáticas simples e
implementar as duas técnicas de derivação automática.
Para isso, seja dado o seguinte tipo de dados,

\begin{code}
data ExpAr a = X
           | N a
           | Bin BinOp (ExpAr a) (ExpAr a)
           | Un UnOp (ExpAr a)
           deriving (Eq, Show)
\end{code}

\noindent
onde |BinOp| e |UnOp| representam operações binárias e unárias, respectivamente:

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

Assim, cada expressão pode ser uma variável, um número, uma operação binária
aplicada às devidas expressões, ou uma operação unária aplicada a uma expressão.
Por exemplo,
\begin{spec}
Bin Sum X (N 10)
\end{spec}
designa |x+10| na notação matemática habitual.

\begin{enumerate}
\item A definição das funções |inExpAr| e |baseExpAr| para este tipo é a seguinte:
\begin{code}
inExpAr = either (const X) num_ops where
  num_ops = either N ops
  ops     = either bin (uncurry Un)
  bin(op, (a, b)) = Bin op a b

baseExpAr f g h j k l z = f -|- (g -|- (h >< (j >< k) -|- l >< z))
\end{code}

  Defina as funções |outExpAr| e |recExpAr|,
  e teste as propriedades que se seguem.
  \begin{propriedade}
    |inExpAr| e |outExpAr| são testemunhas de um isomorfismo,
    isto é,
    |inExpAr . outExpAr = id| e |outExpAr . idExpAr = id|:
\begin{code}
prop_in_out_idExpAr :: (Eq a) => ExpAr a -> Bool
prop_in_out_idExpAr = inExpAr . outExpAr .==. id

prop_out_in_idExpAr :: (Eq a) => OutExpAr a -> Bool
prop_out_in_idExpAr = outExpAr . inExpAr .==. id
\end{code}
    \end{propriedade}

  \item Dada uma expressão aritmética e um escalar para substituir o |X|,
	a função

\begin{quote}
      |eval_exp :: Floating a => a -> (ExpAr a) -> a|
\end{quote}

\noindent calcula o resultado da expressão. Na página \pageref{pg:P1}
    esta função está expressa como um catamorfismo. Defina o respectivo gene
    e, de seguida, teste as propriedades:
    \begin{propriedade}
       A função |eval_exp| respeita os elementos neutros das operações.
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
      Negar duas vezes uma expressão tem o mesmo valor que não fazer nada.
\begin{code}
prop_double_negate :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_double_negate a exp = eval_exp a exp .=?=. eval_exp a (Un Negate (Un Negate exp))
\end{code}
    \end{propriedade}

  \item É possível otimizar o cálculo do valor de uma expressão aritmética tirando proveito
  dos elementos absorventes de cada operação. Implemente os genes da função
\begin{spec}
      optmize_eval :: (Floating a, Eq a) => a -> (ExpAr a) -> a
\end{spec}
  que se encontra na página \pageref{pg:P1} expressa como um hilomorfismo\footnote{Qual é a vantagem de implementar a função |optimize_eval| utilizando um hilomorfismo em vez de utilizar um catamorfismo com um gene "inteligente"?}
  e teste as propriedades:

    \begin{propriedade}
      A função |optimize_eval| respeita a semântica da função |eval|.
\begin{code}
prop_optimize_respects_semantics :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_optimize_respects_semantics a exp = eval_exp a exp .=?=. optmize_eval a exp
\end{code}
    \end{propriedade}


\item Para calcular a derivada de uma expressão, é necessário aplicar transformações
à expressão original que respeitem as regras das derivadas:\footnote{%
	Apesar da adição e multiplicação gozarem da propriedade comutativa,
	há que ter em atenção a ordem das operações por causa dos testes.}

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

  Defina o gene do catamorfismo que ocorre na função
    \begin{quote}
      |sd :: Floating a => ExpAr a -> ExpAr a|
    \end{quote}
  que, dada uma expressão aritmética, calcula a sua derivada.
  Testes a fazer, de seguida:
    \begin{propriedade}
       A função |sd| respeita as regras de derivação.
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

\item Como foi visto, \emph{Symbolic differentiation} não é a técnica
mais eficaz para o cálculo do valor da derivada de uma expressão.
\emph{Automatic differentiation} resolve este problema cálculando o valor
da derivada em vez de manipular a expressão original.

  Defina o gene do catamorfismo que ocorre na função
    \begin{spec}
    ad :: Floating a => a -> ExpAr a -> a
    \end{spec}
  que, dada uma expressão aritmética e um ponto,
  calcula o valor da sua derivada nesse ponto,
  sem transformar manipular a expressão original.
  Testes a fazer, de seguida:

    \begin{propriedade}
       Calcular o valor da derivada num ponto |r| via |ad| é equivalente a calcular a derivada da expressão e avalia-la no ponto |r|.
\begin{code}
prop_congruent :: (Floating a, Real a) => a -> ExpAr a -> Bool
prop_congruent a exp = ad a exp .=?=. eval_exp a (sd exp)
\end{code}
    \end{propriedade}
\end{enumerate}

\Problema

Nesta disciplina estudou-se como fazer \pd{programação dinâmica} por cálculo,
recorrendo à lei de recursividade mútua.\footnote{Lei (\ref{eq:fokkinga})
em \cite{Ol18}, página \pageref{eq:fokkinga}.}

Para o caso de funções sobre os números naturais (|Nat0|, com functor |fF
X = 1 + X|) é fácil derivar-se da lei que foi estudada uma
	\emph{regra de algibeira}
	\label{pg:regra}
que se pode ensinar a programadores que não tenham estudado
\cp{Cálculo de Programas}. Apresenta-se de seguida essa regra, tomando como exemplo o
cálculo do ciclo-\textsf{for} que implementa a função de Fibonacci, recordar
o sistema
\begin{spec}
fib 0 = 1
fib(n+1) = f n

f 0 = 1
f (n+1) = fib n + f n
\end{spec}
Obter-se-á de imediato
\begin{code}
fib' = p1 . for loop init where
   loop(fib,f)=(f,fib+f)
   init = (1,1)
\end{code}
usando as regras seguintes:
\begin{itemize}
\item	O corpo do ciclo |loop| terá tantos argumentos quanto o número de funções mutuamente recursivas.
\item	Para as variáveis escolhem-se os próprios nomes das funções, pela ordem
que se achar conveniente.\footnote{Podem obviamente usar-se outros símbolos, mas numa primeira leitura
dá jeito usarem-se tais nomes.}
\item	Para os resultados vão-se buscar as expressões respectivas, retirando a variável |n|.
\item	Em |init| coleccionam-se os resultados dos casos de base das funções, pela mesma ordem.
\end{itemize}
Mais um exemplo, envolvendo polinómios do segundo grau $ax^2 + b x + c$ em |Nat0|.
Seguindo o método estudado nas aulas\footnote{Secção 3.17 de \cite{Ol18} e tópico
\href{https://www4.di.uminho.pt/~jno/media/cp/}{Recursividade mútua} nos vídeos das aulas teóricas.},
de $f\ x = a x^2 + b x + c$ derivam-se duas funções mutuamente recursivas:
\begin{spec}
f 0 = c
f (n+1) = f n + k n

k 0 = a + b
k(n+1) = k n + 2 a
\end{spec}
Seguindo a regra acima, calcula-se de imediato a seguinte implementação, em Haskell:
\begin{code}
f' a b c = p1 . for loop init where
  loop(f,k) = (f+k,k+2*a)
  init = (c,a+b) 
\end{code}
O que se pede então, nesta pergunta?
Dada a fórmula que dá o |n|-ésimo \catalan{número de Catalan},
\begin{eqnarray}
	C_n = \frac{(2n)!}{(n+1)! (n!) }
	\label{eq:cat}
\end{eqnarray}
derivar uma implementação de $C_n$ que não calcule factoriais nenhuns.
Isto é, derivar um ciclo-\textsf{for}
\begin{spec}
cat = cdots . for loop init where cdots
\end{spec}
que implemente esta função.

\begin{propriedade}
A função proposta coincidem com a definição dada:
\begin{code}
prop_cat = (>=0) .==>. (catdef  .==. cat)
\end{code}
\end{propriedade}
%
\textbf{Sugestão}: Começar por estudar muito bem o processo de cálculo dado
no anexo \ref{sec:recmul} para o problema (semelhante) da função exponencial.


\Problema 

As \bezier{curvas de Bézier}, designação dada em honra ao engenheiro
\href{https://en.wikipedia.org/wiki/Pierre_B%C3%A9zier}{Pierre Bézier},
são curvas ubíquas na área de computação gráfica, animação e modelação.
Uma curva de Bézier é uma curva paramétrica, definida por um conjunto
$\{P_0,...,P_N\}$ de pontos de controlo, onde $N$ é a ordem da curva.

\begin{figure}[h!]
  \centering
  \includegraphics[width=0.8\textwidth]{cp2021t_media/Bezier_curves.png}
  \caption{Exemplos de curvas de Bézier retirados da \bezier{ Wikipedia}.}
\end{figure}

O algoritmo de \emph{De Casteljau} é um método recursivo capaz de calcular
curvas de Bézier num ponto. Apesar de ser mais lento do que outras abordagens,
este algoritmo é numericamente mais estável, trocando velocidade por correção.

De forma sucinta, o valor de uma curva de Bézier de um só ponto $\{P_0\}$
(ordem $0$) é o próprio ponto $P_0$. O valor de uma curva de Bézier de ordem
$N$ é calculado através da interpolação linear da curva de Bézier dos primeiros
$N-1$ pontos e da curva de Bézier dos últimos $N-1$ pontos.

A interpolação linear entre 2 números, no intervalo $[0, 1]$, é dada pela
seguinte função:

\begin{code}
linear1d :: Rational -> Rational -> OverTime Rational
linear1d a b = formula a b where
  formula :: Rational -> Rational -> Float -> Rational
  formula x y t = ((1.0 :: Rational) - (toRational t)) * x + (toRational t) * y
\end{code}
%
A interpolação linear entre 2 pontos de dimensão $N$ é calculada através
da interpolação linear de cada dimensão.

O tipo de dados |NPoint| representa um ponto com $N$ dimensões.
\begin{code}
type NPoint = [Rational]
\end{code}
Por exemplo, um ponto de 2 dimensões e um ponto de 3 dimensões podem ser
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
O anexo \ref{sec:codigo} tem definida a função 
    \begin{spec}
    calcLine :: NPoint -> (NPoint -> OverTime NPoint)
    \end{spec}
que calcula a interpolação linear entre 2 pontos, e a função
    \begin{spec}
    deCasteljau :: [NPoint] -> OverTime NPoint
    \end{spec}
que implementa o algoritmo respectivo.

\begin{enumerate}

\item Implemente |calcLine| como um catamorfismo de listas,
testando a sua definição com a propriedade:
    \begin{propriedade} Definição alternativa.
\begin{code}
prop_calcLine_def :: NPoint -> NPoint -> Float -> Bool
prop_calcLine_def p q d = calcLine p q d ==  zipWithM linear1d p q d
\end{code}
    \end{propriedade}

\item Implemente a função |deCasteljau| como um hilomorfismo, testando agora a propriedade:
    \begin{propriedade}
      Curvas de Bézier são simétricas.
\begin{code}
prop_bezier_sym :: [[Rational]] -> Gen Bool
prop_bezier_sym l = all (< delta) . calc_difs . bezs <$> elements ps  where
  calc_difs = (\(x, y) -> zipWith (\w v -> if w >= v then w - v else v - w) x y)
  bezs t    = (deCasteljau l t, deCasteljau (reverse l) (fromRational (1 - (toRational t))))
  delta = 1e-2
\end{code}
    \end{propriedade}

  \item Corra a função |runBezier| e aprecie o seu trabalho\footnote{%
        A representação em Gloss é uma adaptação de um
        \href{https://github.com/hrldcpr/Bezier.hs}{projeto}
        de Harold Cooper.} clicando na janela que é aberta (que contém, a verde, um ponto
        inicila) com o botão esquerdo do rato para adicionar mais pontos.
        A tecla |Delete| apaga o ponto mais recente.

\end{enumerate}

\Problema

Seja dada a fórmula que calcula a média de uma lista não vazia $x$,
\begin{equation}
avg\ x = \frac 1 k\sum_{i=1}^{k} x_i
\end{equation}
onde $k=length\ x$. Isto é, para sabermos a média de uma lista precisamos de dois catamorfismos: o que faz o somatório e o que calcula o comprimento a lista.
Contudo, é facil de ver que
\begin{quote}
	$avg\ [a]=a$
\\
	$avg (a:x) = \frac 1 {k+1}(a+\sum_{i=1}^{k} x_i) = \frac{a+k(avg\ x)}{k+1}$ para $k=length\ x$
\end{quote}
Logo $avg$ está em recursividade mútua com $length$ e o par de funções pode ser expresso por um único catamorfismo, significando que a lista apenas é percorrida uma vez.

\begin{enumerate}

\item	Recorra à lei de recursividade mútua para derivar a função
|avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length| em listas não vazias. 

\item	Generalize o raciocínio anterior para o cálculo da média de todos os elementos de uma \LTree\ recorrendo a uma única travessia da árvore (i.e.\ catamorfismo).

\end{enumerate}
Verifique as suas funções testando a propriedade seguinte:
\begin{propriedade}
A média de uma lista não vazia e de uma \LTree\ com os mesmos elementos coincide,
a menos de um erro de 0.1 milésimas:
\begin{code}
prop_avg :: [Double] -> Property
prop_avg = nonempty .==>. diff .<=. const 0.000001 where
   diff l = avg l - (avgLTree . genLTree) l
   genLTree = anaLTree lsplit
   nonempty = (>[])
\end{code}
\end{propriedade}

\Problema	(\textbf{NB}: Esta questão é \textbf{opcional} e funciona como \textbf{valorização} apenas para os alunos que desejarem fazê-la.) 

\vskip 1em \noindent
Existem muitas linguagens funcionais para além do \Haskell, que é a linguagem usada neste trabalho prático. Uma delas é o \Fsharp\ da Microsoft. Na directoria \verb!fsharp! encontram-se os módulos \Cp, \Nat\ e \LTree\ codificados em \Fsharp. O que se pede é a biblioteca \BTree\ escrita na mesma linguagem.

Modo de execução: o código que tiverem produzido nesta pergunta deve ser colocado entre o \verb!\begin{verbatim}! e o \verb!\end{verbatim}! da correspondente parte do anexo \ref{sec:resolucao}. Para além disso, os grupos podem demonstrar o código na oral.

\newpage

\part*{Anexos}

\appendix

\section{Como exprimir cálculos e diagramas em LaTeX/lhs2tex}
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

Os diagramas podem ser produzidos recorrendo à \emph{package} \LaTeX\ 
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

\section{Programação dinâmica por recursividade múltipla}\label{sec:recmul}
Neste anexo dão-se os detalhes da resolução do Exercício \ref{ex:exp} dos apontamentos da
disciplina\footnote{Cf.\ \cite{Ol18}, página \pageref{ex:exp}.},
onde se pretende implementar um ciclo que implemente
o cálculo da aproximação até |i=n| da função exponencial $exp\ x = e^x$,
via série de Taylor:
\begin{eqnarray}
	exp\ x 
& = &
	\sum_{i=0}^{\infty} \frac {x^i} {i!}
\end{eqnarray}
Seja $e\ x\ n = \sum_{i=0}^{n} \frac {x^i} {i!}$ a função que dá essa aproximação.
É fácil de ver que |e x 0 = 1| e que $|e x (n+1)| = |e x n| + \frac {x^{n+1}} {(n+1)!}$.
Se definirmos $|h x n| = \frac {x^{n+1}} {(n+1)!}$ teremos |e x| e |h x| em recursividade
mútua. Se repetirmos o processo para |h x n| etc obteremos no total três funções nessa mesma
situação:
\begin{spec}
e x 0 = 1
e x (n+1) = h x n + e x n

h x 0 = x
h x (n+1) = x/(s n) * h x n

s 0 = 2
s (n+1) = 1 + s n
\end{spec}
Segundo a \emph{regra de algibeira} descrita na página \ref{pg:regra} deste enunciado,
ter-se-á, de imediato:
\begin{code}
e' x = prj . for loop init where
     init = (1,x,2)
     loop(e,h,s)=(h+e,x/s*h,1+s)
     prj(e,h,s) = e
\end{code}

\section{Código fornecido}\label{sec:codigo}

\subsection*{Problema 1}

\begin{code}
expd :: Floating a => a -> a
expd = Prelude.exp

type OutExpAr a = Either () (Either a (Either (BinOp, (ExpAr a, ExpAr a)) (UnOp, ExpAr a)))
\end{code}

\subsection*{Problema 2}
Definição da série de Catalan usando factoriais (\ref{eq:cat}):
\begin{code}
catdef n = div (fac((2*n))) ((fac((n+1))*(fac n)))
\end{code}
Oráculo para inspecção dos primeiros 26 números de Catalan\footnote{Fonte:
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
Função auxiliar:
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
Animação:
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
runBezier = play (InWindow "Bézier" (600, 600) (0,  0))
  black 50 initW picture actions tick

runBezierSym :: IO ()
runBezierSym = quickCheckWith (stdArgs {maxSize = 20, maxSuccess = 200} ) prop_bezier_sym
\end{code}

Compilação e execução dentro do interpretador:\footnote{Pode ser útil em testes
envolvendo \gloss{Gloss}. Nesse caso, o teste em causa deve fazer parte de uma função
|main|.}
\begin{code}
main = runBezier

run = do { system "ghc cp2021t" ; system "./cp2021t" }
\end{code}

\subsection*{QuickCheck}
Código para geração de testes:
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

\subsection*{Outras funções auxiliares}
%----------------- Outras definições auxiliares -------------------------------------------%
Lógicas:
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

%----------------- Soluções dos alunos -----------------------------------------%

\section{Soluções dos alunos}\label{sec:resolucao}
Os alunos devem colocar neste anexo as suas soluções para os exercícios
propostos, de acordo com o "layout" que se fornece. Não podem ser
alterados os nomes ou tipos das funções dadas, mas pode ser adicionado
texto, disgramas e/ou outras funções auxiliares que sejam necessárias.

Valoriza-se a escrita de \emph{pouco} código que corresponda a soluções
simples e elegantes. 

\subsection*{Problema 1} \label{pg:P1}
São dadas:
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
\subsection{Solução: }
Uma vez que estamos a trabalhar com um tipo indutivo novo iremos representar o diagrama genérico de um catamorfismo que atua sobre o tipo indutivo ExprAr. Além disso, iremos representar o bifunctor de base bem como a função out associada a este tipo indutivo.

Pela análise da função |baseExprAr| conseguimos perceber de um modo geral como o bifunctor de base atua. 
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

Como em qualquer catamorfismo, está presente o isomorfismo in- out e pelas leis de Cálculo de Programas, conseguimos obter a definição da função outExpAr.

\textbf{NB}: Por efeitos de simplificação, iremos referir a função |outExpAr| como apenas |out|.

Temos:

\begin{eqnarray*}
\start
  |out . inExpAr = id|
%
\just\equiv{ Definição de |inExpAr| }
%
|out . (either (const X) num_ops) = id|
%
\just\equiv{ Definição de |num_ops| }
%
|out . (either (const X) (either N ops))|
%
\just\equiv{ Definição de |ops| }
%
|out . (either (const X) (either N (either bin (uncurry Un))))|
%
\just\equiv{ Fusão + (20) }
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
\just\equiv{ Ig Existencial (71), Def de Composição (72), Def de Const (74), Def de Uncurry (84), Def de |Un|, Def |Bin|}
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
\subsection{Solução: }
Pela análise do diagrama, percebemos como a recursividade, isto é, como um catamorfismo associado a este tipo indutivo "consome" a estrutura de dados. Temos também o functor do tipo indutivo dado pela função |baseExpAr|.

Assim conseguimos chegar de forma indutiva à definição da função recExpAr:
\begin{code}
recExpAr f= baseExpAr id id id f f id f
\end{code}
\subsection{Solução: }
Dada a situação em que nos é dado um escalar e uma expressão, ao termos de calcular o valor da mesma, substituindo o valor do escalar de forma apropriada à expressão, conseguimos mais uma vez através da análise do diagrama perceber como a recursividade está explícita neste caso.
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

É de salientar que o ponto fulcral do problema é induzir o gene do catamorfismo |eval_exp|, ou seja "descobrir" como definir a função |g_eval_exp|.
Ora consoante o tipo de |ExpAr| em  causa e um escalar, de forma a calcular o valor da expressão para esse escalar, temos uma das seguintes possibilidades ou até mesmo várias das seguintes possibilidades:

\begin{itemize}
  \item Caso 1: Uma expressão ser uma incógnita |x| e dado um escalar, o valor da expressão é o próprio escalar;
\end{itemize}
\begin{code}
g_eval_exp escalar (Left ()) = escalar
\end{code}
\begin{itemize}
  \item Caso 2: Uma expressão ser um escalar |valor| e dado um escalar, o valor da expressão é o próprio |valor|;
\end{itemize}
\begin{code}
g_eval_exp escalar (Right (Left valor)) = valor
\end{code}
\begin{itemize}
  \item Caso 3: Uma expressão ser uma soma/produto entre dois |ExpAr| e dado um escalar, o valor da expressão é somar/multiplicar os dois |ExpAr|, substituindo as incógnitas pelo escalar;
\end{itemize}
\textbf{NB}: É de salientar que ambos os |ExpAr| supramencionados foram já processados pelo catamorfismo e as incógnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code} 
g_eval_exp escalar (Right(Right(Left (Sum,(a,b))))) = a + b
g_eval_exp escalar (Right(Right(Left (Product,(a,b))))) = a * b
\end{code}
\begin{itemize}
  \item Caso 4: Uma expressão ser uma negação de um |ExpAr| e dado um escalar, o valor da expressão é negar o |ExpAr|, substituindo as incógnitas pelo escalar;
\end{itemize}
\textbf{NB}: É de salientar que o |ExpAr| supramencionado foi já processado pelo catamorfismo e as incógnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code}
g_eval_exp escalar (Right(Right(Right (Negate, a)))) = (-1) * a 
\end{code}
\begin{itemize}
  \item Caso 5: Uma expressão ser uma base de |e| cujo expoente é um |ExpAr| e dado um escalar, o valor da expressão é elevar a base |e| ao expoente |ExpAr|, substituindo as incógnitas pelo escalar;
\end{itemize}
\textbf{NB}: É de salientar que o |ExpAr| supramencionado foi já processado pelo catamorfismo e as incógnitas substituidas pelo valor do escalar, na recursividade quando esta chega aos casos de base (caso 1 e caso 2).
\begin{code}
g_eval_exp escalar (Right(Right(Right (E, a)))) = Prelude.exp a
\end{code}

\subsection{Solução: }
De forma a tirar proveito das propriedades dos elementos absorventes e neutros das operações matemáticas impostas no tipo indutivo em causa, teremos de analisar os vários casos em que conseguimos "limpar" uma expressão. Além disso, a maneira que iremos trabalhar com estes casos é a mesma para a função |outExpAr| associada a este tipo indutivo, uma vez que iremos apenas receber uma |ExpAr| e a iremos "limpar".
Assim, consoante o tipo |ExpAr| em causa, de forma a tirar proveito das propriedades dos elementos neutro e absorventes temos uma das seguintes possibilidades ou até mesmo várias das seguintes possibilidades:
\begin{itemize}
  \item Caso 1: Uma expressão ser um produto de uma |ExpAr| com 0 é o mesmo que apenas ter 0, tirando proveito da propriedade do elemento absorvente da multiplicação;
\end{itemize}
\begin{code}
clean (Bin Product a (N 0)) = outExpAr (N 0)
clean (Bin Product (N 0) a) = outExpAr (N 0)
\end{code}
\begin{itemize}
  \item Caso 2: Uma expressão ser a base de |e| cujo expoente é 0 é o mesmo que apenas ter 1, tirando proveito da propriedade do elemento absorvente da exponeciação;
\end{itemize}
\begin{code}
clean (Un E (N 0)) = outExpAr (N 1)
\end{code}
\begin{itemize}
  \item Caso 3: Uma expressão ser a negação de 0 é o mesmo que apenas ter 0, tirando proveito da propriedade do elemento neutro da negação;
\end{itemize}
\begin{code}
clean (Un Negate (N 0)) = outExpAr (N 0)
\end{code}
\begin{itemize}
  \item Caso 4: Uma expressão que à partida não tira proveito de nenhuma das propriedades supramencionadas, terá de ser analisada nas suas partes, sendo esta análise já efetuada aquando da recursividade;
\end{itemize}
\emph{Caso 5}: Uma expressão que à partida não tira proveito de nenhuma das propriedades supramencionadas, terá de ser analisada nas suas partes, sendo esta análise já efetuada aquando da recursividade;
\begin{code}
clean x = outExpAr x
\end{code}

A função gopt "consome", isto é, calcula apenas a expressão, fazendo uso da função |g_eval_exp| acima definida.
\begin{code}
gopt exp = g_eval_exp exp 
\end{code}
Ora é de ressalvar, que pela a análise da definição do hilomorfismo associado a este tipo indutivo, |hyloExpAr|, vemos que a função que "constroi" a estrutura de dados, que desempenha o papel de anamorfismo, é a função |clean| e a função que consome esta estrutura intermédia criada pela função |clean| é a função |gopt| que desempenha o papel de catamorfismo.

\subsection{Solução: }
Uma vez que queremos calcular a derivada de uma expressão, teremos de ter em conta os vários casos possíveis e que se adequam ao tipo indutivo em causa e que estão presentes na matemática que aprendemos no ensino básico. Além disso, pelas regras que nos são apresentadas como ponto de partida, conseguimos perceber que iremos lidar com um catamorfismo, que terá casos de base e casos recursivos, sendo que estes últimos já serão processados pelo próprio catamorfismo |sd|. 
Primeiramente iremos analisar a tipagem da função |sd_gen| que irá tratar do cálculo da derivada de uma expressão do tipo |ExpAr|.
\begin{code}
sd_gen :: Floating a =>
    Either () (Either a (Either (BinOp, ((ExpAr a, ExpAr a), (ExpAr a, ExpAr a))) (UnOp, (ExpAr a, ExpAr a)))) -> (ExpAr a, ExpAr a)
\end{code}
Ao analisar a tipagem da função |sd_gen| ficamos com uma dúvida: "O que são os pares de |ExpAr| nos operadores |Bin| e |Un|?".

Sabemos que estamos perante um gene de catamorfismo e que teremos casos em que, dado o operador em causa, temos argumentos por processar, isto é, por calcular a sua derivada. Pela tipagem percebemos que o catamorfismo em causa pede os tais dois pares e pela a análise das regras de derivação, percebemos que a primeira componente de cada par é a expressão que ainda não foi derivada e a segunda componente é a expressão que já foi derivada.
Assim, consoante o tipo |ExpAr| em causa, seguindo as regras de derivação temos uma das seguintes possibilidades ou até mesmo várias das seguintes possibilidades:

\begin{itemize}
  \item Caso 1: Regra da derivada de uma incógnita:
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
  \item Caso 5: Regra da derivada de uma negação:
\end{itemize}
\begin{code}
sd_gen (Right(Right(Right (Negate, (a, b))))) = (Un Negate a, Un Negate b)
\end{code}
\begin{itemize}
  \item Caso 6: Regra da derivada de uma expressão cuja base é |e|:
\begin{eqnarray*}
  \frac{d}{dx}{e^a}= {e^a}\cdot \frac{d}{dx}(a)
\end{eqnarray*}
\end{itemize}
\begin{code}
sd_gen (Right(Right(Right (E, (a, b))))) = (Un E a, Bin Product (Un E a) b)
\end{code}

\subsection{Solução: }
Sabemos que estamos perante um gene de catamorfismo e que teremos casos em que, dado o operador em causa, temos argumentos por processar, isto é, por calcular a sua derivada. Além disso, agora é nos dados um escalar de forma a calcularmos a derivada no ponto (escalar) dado, sem manipular ou transformar a expressão em causa. Assim, consoante o tipo |ExpAr| em causa, seguindo as regras de derivação temos uma das seguintes possibilidades ou até mesmo várias das seguintes possibilidades: 
\begin{itemize}
  \item Caso 1: Regra da derivada de uma incógnita:
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
  \item Caso 5: Regra da derivada de uma negação:
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Right (Negate, (a, b))))) = (a * (-1), b * (-1))
\end{code}
\begin{itemize}
  \item Caso 6: Regra da derivada de uma expressão cuja base é |e|:
\begin{eqnarray*}
  \frac{d}{dx}{e^a}= {e^a}\cdot \frac{d}{dx}(a)
\end{eqnarray*}
\end{itemize}
\begin{code}
ad_gen x (Right(Right(Right (E, (a, b))))) = (Prelude.exp a, b * (Prelude.exp a))
\end{code}

\subsection*{Problema 2}
\subsection*{Solução:}
Uma vez que queremos derivar uma implementação da fórmula de Catalan, (função |Cn|) sem fatoriais, teremos de descobrir alguma "propriedade" da mesma. Ora a base desta "propriedade" já nos é que é a recursividade mútua. Assim, teremos de chegar a uma fórmula que expresse recursividade mútua,tendo como ponto de partida a fórmula que dá o n-ésimo número de Catalan:
\begin{eqnarray*}
\start
|C n = (2n)!/((n+1)! >< (n!))|
%
\qed
\end{eqnarray*}

Ao analisarmos a fórmula e ao estarmos a trabalhar nos |Nat0|, conseguimos inferir o caso base e o caso recursivo da fórmula de Catalan.
Assim, temos o caso base e o caso recursivo abaixo representados respetivamente:
\begin{eqnarray*}
\start
\just\equiv{ Definição do caso base, Definição do caso recursivo (para n + 1)}
%
      \begin{lcbr}
          |C 0 = 0!/(1! >< 0!)|\\
          |C(n+1)= Cn >< (2n+2)!/ ((n+2)!(n+1)!)|\\
      \end{lcbr}
%
\just\equiv{ Simplificação do caso base, Propriedade do factorial (|x! = x >< (x - 1)!|) }
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
\just\equiv{ Definição de |C n = (2n)!/ ((n!) >< (n+1)!)| }
%
      \begin{lcbr}
          |C 0 =1|\\
          |C(n+1)= Cn >< ((2n+2) >< (2n+1))/((n+2) >< (n+1))|\\
      \end{lcbr}
%
\just\equiv{ Colocar o 2 em evidência }
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
\just\equiv{ Intrudução das funções |f| e |g| }
%
      \begin{lcbr}
          |C 0 =1|\\
          |C(n+1)= Cn ><  f(n)/g(n)|\\
      \end{lcbr}
%
\qed
\end{eqnarray*}

\textbf{NB}: Criamos duas funções de forma a simplificar o cálculo, em que a função |f| é o numerador e a função |g| é o denominador.
Tendo:

|f(n)= 2(2n+1)|

|g(n)= n+2|

Uma vez definidas as funções "auxiliares", conseguimos também definir os casos base das mesma. Tal como referido anteriormente, como estamos nos |Nat0|, conseguimos induzir facilmente os casos base das funções e álém disso, simplificar as mesmas, tendo-se:
\begin{eqnarray*}
\start
\just\equiv{ Definição de |f|, Definição de |g| }
%
      \begin{lcbr}
          |f(n)= 2(2n+1)|\\
          |g(n)= n+2|\\
      \end{lcbr}
%
\just\equiv{ Definição do caso base e recursivo de |f|, Definição do caso base e recursivo de |g| }
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
\just\equiv{ Simplificação do caso recursivo de |f| }
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
\just\equiv{ Definição de |f n = 2(2n+1)|, Definição de |g n = n+2| }
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
Após a simplificação da fórmula de Catalan dada, conseguimos chegar a uma expressão que não depende de factoriais. Ao analisar em detalhe, percebemos algo fulcral, que é a existência de recursividade mútua nesta nova expressão.

Estamos prontos para usar a dica que nos foi dado no enunciado, usando a função |loop|. Segundo o enunciado, na primeira etapa "O corpo do ciclo loop terá tantos argumentos quanto o número de funções mutuamente recursivas.", ora as funções mutuamente recursivas serão 3 sendo que 2 delas formarão um par (as funções |f| e |g|). Seguindo a segunda etapa "Para as variáveis escolhem-se os próprios nomes das funções, pela ordem que se achar conveniente", sendo que os argumentos da função |loop| serão as funções mutuamente recursivas |f|, |g| e |C|. Com estas etapas juntamente com a terceira etapa, temos a definição da função |loop|:
\begin{eqnarray*}
\start
|loop (C,(f,g)) = ((C*f)/g ,(f+4, g+1))|
\qed
\end{eqnarray*}

\textbf{NB}: É de salientar que a função |loop| é quem vai tratar da recursividade mútua das várias funções em causa (|f|, |g|, |C|);

Ao chegarmos à etapa final, a função init vai recolher os casos bases pela mesma ordem que as funções argumentos aparecem na função |loop|. Assim e analisando os cálculos acima, temos a definição da função |init|: 
\begin{eqnarray*}
\start
|init = (1, 2, 2)|
\qed
\end{eqnarray*}

Baseando-nos no exemplo aplicamos também a função |p1| após o |for loop init|, obtendo:
\begin{eqnarray*}
\start
|cat = p1 . for loop init|
\qed
\end{eqnarray*}
Assim, obtemos as definições das funções supramencionadas:
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
seja a função pretendida.
\textbf{NB}: usar divisão inteira.
Apresentar de seguida a justificação da solução encontrada.
\subsection*{Problema 3}
\subsection{Solução: }
Uma vez que a função |calcLine| calcula a interpolação linear entre dois pontos e cada um destes pontos é do tipo |NPoint| que por sua vez é uma lista de |Rational| de tamanho |N|, sendo |N| o número de dimensões de cada ponto, temos que a função |calcLine| é um catamorfismo tal é referido no enunciado, que irá "consumir" as dimensões em causa. Dado que o tipo em causa "consome" listas de |Rational| conseguimos perceber e inferir que o bifunctor de base associado a este tipo indutivo é o mesmo que é usado para o tipo indutivo |List|. Assim temos:

  |T A = NPoint|

  |B(X, Y) = X + X >< Y|

  |B(id, f) = id + id >< f|

De seguida, iremos definir o diagrama genérico associado ao tipo indutivo |NPoint|:

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

Com a informação do diagrama acima, conseguimos inferir o diagrama associado ao catamorfismo |calcLine|:
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

Como foi referido anteriormente, uma vez que a função |calcLine| é um catamorfismo, falta-nos induzir o gene |h| associado a este catamorfismo. Conseguimos perceber através da dica dada no anexo \ref{sec:codigo}, que o gene irá fazer uso da função |g| disponibilizada para tratar do que vem da recursividade. Assim, conseguimos chegar à definição da função |calcLine| através do seu gene.
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
\subsection{Solução: }
\begin{code}
deCasteljau :: [NPoint] -> OverTime NPoint
deCasteljau = hyloAlgForm alg coalg where
   coalg = undefined
   alg = undefined

hyloAlgForm = undefined
\end{code}

\subsection*{Problema 4}

\subsection{ Solução para listas não vazias:}

Uma vez que estamos a trabalhar com listas não vazias teremos que definir um tipo indutivo para tal.Ora este irá ser muito semelhante ao já conhecido tipo indutivo List.
Assim temos: 

  |T A = NotEmptyList A|

  |B(X, Y) = X + X >< Y|

  |B(id, f) = id + id >< f|

Diagrama genérico de um catamorfismo sobre o tipo indutivo |NotEmptyList|:
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
Além disso, teremos de definir a função out assim como a função que caracteriza o comportamento recursivo de um catamorfismo sobre o tipo indutivo supramencionado. Deste modo temos:

\begin{code}

outNotEmptyList [a]    = i1 (a)
outNotEmptyList (a:x) = i2(a,x)

recNotEmptyList  f   = id -|- id >< f 

cataNotEmptyList g = g . recNotEmptyList (cataNotEmptyList g) . outNotEmptyList
\end{code}

 Uma vez que temos na alínea 1 do enunciado do Problema: |avg_aux = cata (either b q)| tal que 
|avg_aux = split avg length|
para listas não vazias, teremos primeiro de definir o gene da função length e da função avg para o tipo indutivo em causa. Assim temos, para a função length: 

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

E para a a função avg, temos:
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

Em que |x| é a cauda da lista.

\textbf{NB}: Para efeito de simplificação, usaremos o gene do catamorfismo avg como  |either g1 g2|.

Uma vez que queremos usar a lei de recursividade mútua, temos como ponto de partida a seguinte expressão:

  |avg_aux = split avg length|

Onde o diagrama da função |avg_aux| é o seguinte:

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

Assim, teremos de aplicar as leis do Cálculo de Programas:
\begin{eqnarray*}
\start
|avg_aux = split avg length|
%
\just\equiv{ Definição de avg como catamorfismo, definição de length como catamorfismo }
%
|avg_aux = split (either g1 g2) (either one (succ.p2))|
%
\just\equiv{ Lei Banana-Split (53) }
%
|avg_aux = cata (((either g1 g2) >< (either one (succ.p2))) . split (F p1) (F p2)|
%
\just\equiv{ Definição de Functor para |NotEmptyList| }
%
|avg_aux = cata ((either g1 g2) >< (either one (succ . p2)) .  split (id + (id >< p1)) (id + (id >< p2)))|
%
\just\equiv{ Lei Absorção x (11) }
%
|avg_aux = cata (split ((either g1 g2). (id + id >< p1)) ((either one (succ.p2)). (id + id >< p2)))|
%
\just\equiv{ Lei Absorção + (22), Natural id (1), natural |p2| (13) }
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
Desta forma chegámos ao pretendido:
|avg_aux = cata (either b q)|

Com

|b = split g1 one|

|q = split (g2.(id >< p1)) (succ.p2.p2)|

E substituindo pelas definições de g1 e g2, temos:

|b = split id one|

|q = split av len|

Onde:

|av = uncurry div (uncurry add (p1,(uncurry mul (p2, k))), succ k). (id >< p1)|

|len = succ.p2.p2|

Com isto, temos então definida a função |avg_aux| sobre a forma de um catamorfismo.

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

\subsection{ Solução para árvores de tipo \LTree: }

Ora, após o raciocínio para o tipo indutivo |NotEmptyList|, o raciocínio para o tipo indutivo \LTree\ é o mesmo.

\textbf{NB}: A diferença é que para este tipo indutivo temos que a média só é calculada nas folhas e temos de ir somando o comprimento das sub-árvores (ramo da esquerda e ramo da direita).

Assim temos que a função |avgLTree| é um split de catamorfismos. Logo, temos o seguinte diagrama:

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

Seguindo o mesmo raciocínio, mas aplicado ao tipo indutivo \LTree\ temos agora dois pares obtidos através da recursividade mútua das funções length e avg para este tipo indutivo. Assim cada par é constituido pela média das folhas e comprimento das sub-árvores.

\begin{code}
avgLTree = p1.cataLTree gene where
   gene = either b q 
   b = split id (const 1)
   q = split av len
   av((med_l, comp_l), (med_r, comp_r)) = (med_l * comp_l + med_r *comp_r) / (comp_l + comp_r)
   len((med_l, comp_l), (med_r, comp_r)) = comp_l + comp_r


\end{code}

\subsection*{Problema 5}
Inserir em baixo o código \Fsharp\ desenvolvido, entre \verb!\begin{verbatim}! e \verb!\end{verbatim}!:

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
    by the French mathematician Édouard Lucas, under the pseudonym
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
    
    There is a well­known inductive solution to the problem given
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
    values, true representing a clockwise movement and false an anti­clockwise
    movement. The pair (k,d') means move the disk numbered k from
    its current position in the direction d'. The semicolon operator
    concatenates sequences together, [] denotes an empty sequence
    and [x] is a sequence with exactly one element x. Taking the pairs
    in order from left to right, the complete sequence H n d prescribes
    how to move the n smallest disks one­by­one from one pole to the
    next pole in the direction d following the rule of never placing
    a larger disk on top of a smaller disk.
    
    H 0     d = [],
    H (n+1) d = H n ¬d ; [ (n, d) ] ; H n ¬d.
    
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

%----------------- Fim do anexo com soluções dos alunos ------------------------%

%----------------- Índice remissivo (exige makeindex) -------------------------%

\printindex

%----------------- Bibliografia (exige bibtex) --------------------------------%

\bibliographystyle{plain}
\bibliography{cp2021t}

%----------------- Fim do documento -------------------------------------------%
\end{document}
