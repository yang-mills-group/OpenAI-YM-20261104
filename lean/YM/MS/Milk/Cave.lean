import YM.MS.Milk.Honey
import YM.Next.RANK.GaussLeg
import YM.MS.Awning.Press
/-!
# Free Wilsonian solution ($MS physics$) in coordinate kernel.Design any actual alphabet
 and full cost constraints. Use signed Wick polynomial operations (Next.RANK.NORMAL).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell
open Tensor (diagonal)
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X:Type}{G:Gauge}{n d r:ℕ}{s:ℝ}{f:ℝ→ℂ}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
variable {W E I:Type}{L:Album X G}{U V:ℝ→Law G}{g:X→Normal.poly X}
variable {u v:ℝ→ Normal.Symmetric X}{Q:Normal.Symmetric X}
-- root χ
open Labels Awning Logarithm
open Rake.Geo
abbrev card0 (u:Key G):= singer ( Theater.lamp u )
lemma νb (u:Key G): card0 u∈ Roof G:= ⟨ Wallet.faith ( shadow_ω u ), lying ( shadow_ω u ).1 ⟩
lemma rankC (u:Key G): Book.rank 1 (card0 u):= by intro l hk; rcases l with _|⟨i,_|v⟩; rfl; exfalso; apply hk; rw [mod_int]; rfl; rfl
-- one-site programs with a constant shift
def RawS (G:Gauge) (x:QP): Album (Key G) G where
    H i:= chair G x (card0 i)
    cost i:= chair_p x (νb i)
    line i:= fun l hl=>by rw [seated,rankC i l hl,mul_zero]
def Bend (G:Gauge)(s:ℝ) : Normal.Symmetric (Key G) where
    cov i j:= -(pastK i j 0 s)
    symm i j:= by apply congr_arg (-·); exact Eq.symm (by simpa only [neg_zero] using star_k i j 0 s)
lemma RealB (G:Gauge)(x:QP): Standard ( RawS G x ) (Bend G):= by
    constructor; intro i j s; obtain h:=( ( ClockCert i j ).speak ( fixF x ) ( fixF x ) s ).neg; simpa only [sub_self, LinearEquiv.apply_symm_apply,neg_neg] using! h -- $defeq$
lemma readB (G:Gauge)(x:QP)(p:Pol G): bowl (RawS G x) p= chair G x (Theater.orbit G p):= by
    induction p using MvPolynomial.induction_on with
    | C c=> rw [t_C, cus,coin_s]
    | add p q hp hq=> simp only [map_add,hp,hq]
    | mul_X p i h=> rw [ t_M,t_X,bags,cusp,chair_product,h ]; rfl
lemma costB (i j:Key G): Tendsto (fun s=> (Bend G s).cov i j) atTop (𝓝 0):= by simpa only [ neg_zero ] using! ( eitherI ( ClockCert i j|>.wind 0 ) ( by unfold Drops.sizeL; omega ) ).neg
lemma stableB (p:Pol G)(q:QP)(w:Legs ( Lane4 G )): Tendsto (fun s=> arc p (RawS G q) (Bend G) s w) atTop (𝓝 ( chair G q (Theater.orbit G p) w )):= by obtain h:= last atTop (u:= Bend G) ( L:= RawS G q ) ( Q:=0 ) costB p w; rw [ Tint,LinearMap.comp_apply,Normal.froze,readB ] at h; exact h
end YM.MS.Milk
