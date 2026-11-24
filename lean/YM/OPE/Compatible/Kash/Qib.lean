import YM.OPE.Compatible.Kash.Trill
import YM.OPE.Compatible.Kash.Lease
import YM.OPE.Compatible.Kash.Sump
import YM.OPE.Compatible.Glim.Xpand
/-! # Uniform supplies of finite-angular scripts. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Page
variable {i j d k m r l:ℕ}{Z I J:Type}
variable {n:Side}{x t:ℝ}
local notation "C!"=> Curtain (Shade G)
local notation "Φ" n:arg=>Bid.Dir G n
variable {Γ:Z→ℝ}{g:Filter Z}
lemma readsL {v:Z→ℝ}{N B:Z→ℕ}(hp:Tendsto Γ g atTop)(hz:RateLE g Γ v 0)(hv:RateLE g Γ (fun i=>(N i:ℝ)) 0)(ht:RateLE g Γ (fun i=>(B i:ℝ)) 0)(k:ℕ): RateLE g Γ (fun i=> grain (v i) (N i) (B i) k) 0:=by
        induction k with
        | zero=> exact hz
        | succ k ih=> exact (hv.mul (((RateLE.const _ hp |>.mul ht).mul ih))).mono (by norm_num)
variable {I:Z→Type}[∀ i,Fintype (I i)] (p:(i:Z)→I i→RootEdge)(F:(i:Z)→Libra.Keys G (I i)→ℝ)
structure Arid (Γ:Z→ℝ)(g:Filter Z){I:Z→Type}[∀ i,Fintype (I i)] (p:(i:Z)→I i→RootEdge): Prop where
       count : RateLE g Γ (fun i=>(Fintype.card (I i):ℝ)) 0
       price :∃ B:Z→ℕ, RateLE g Γ (fun i=>(B i:ℝ)) 0 ∧∀ᶠ i in g,∀ j:I i,1+size (p i j).1  ≤  B i
def Tonic (Γ:Z→ℝ)(g:Filter Z)(F:(i:Z)→Libra.Keys G (I i)→ℝ)(k:ℕ):Prop := ∃ b:Z→ℝ, RateLE g Γ b 0∧∀ᶠ i in g, Wallet (F i) k (b i)
variable (hx:Tendsto Γ g atTop)
include hx
lemma trunkN (hz:RateLE g Γ (fun i=>(Fintype.card (I i):ℝ)) 0){p:Z→ℝ}(hp:RateLE g Γ p 0){s:Z→ℕ}(hs:RateLE g Γ (fun i=>(s i:ℝ)) 0): RateLE g Γ (fun i=>grain (p i) (Fintype.card (I i×G.ColorIndex)) (s i^k) l) 0:=by
       have hv:RateLE g Γ (fun i=>(Fintype.card (I i×G.ColorIndex):ℝ)) 0:=by simp_rw [Fintype.card_prod,Nat.cast_mul]; exact (hz.mul (RateLE.const _ hx)).mono (by norm_num)
       apply readsL hx hp hv; simp_rw [Nat.cast_pow]; simpa only[mul_zero] using hs.pow k hx
variable (hK:Arid Γ g p)(ht:∀ i,ContDiffAt ℝ ω (F i) 0)
include hK ht
lemma goan (hp:Tonic Γ g F k): Gusto Γ g (fun i n x=> jet (F i ∘ dip (p i) n x) k) k m:=by
        obtain ⟨b,hb,H⟩:=hK.price; obtain ⟨s,hs,h⟩:=hp; refine ⟨_,trunkN (k:=m) (l:=k) (G:=G) hx hK.count hs hb,(H.and h).mono fun i hi=>?_⟩; exact Twins (F i) (ht i) _ _ _ (p i) (fun j=> Nat.pow_le_pow_left (hi.1 j) _) hi.2
lemma Pride (hp:Tonic Γ g F k)(e:RootEdge)(w:G.ColorIndex): Gusto Γ g (fun i n x v=> fderiv ℝ (jet (F i∘dip (p i) n x) k) v (functorE x e w)) k m:=by
        cases k with
        | zero=> refine (Gusto.Zero hx).Congurs (Eventually.of_forall fun i=>?_); filter_upwards with n; funext x y; rw [show jet (F i∘dip (p i) n x) 0=fun _=>(F i∘dip (p i) n x) 0 from funext fun j=> jet_zero .., fderiv_const_apply]; rfl
        | succ k=>
           obtain ⟨b,hb,H⟩:=hK.price; obtain ⟨s,hs,h⟩:=hp; let htS:=trunkN (k:=m) (l:=k) (G:=G) hx hK.count hs hb; refine ⟨_,((RateLE.const ‖((k:ℝ)+1)‖ hx).mul htS).mono (by norm_num),(H.and h).mono (fun i hi=>?_ )⟩; exact (Picks (F i) (ht i) k (b i^m) m (p i) (fun j=>Nat.pow_le_pow_left (hi.1 j) _) hi.2 e w).taller le_rfl (Nat.le_succ k)
omit ht
variable (e: RootEdge)(b:Bool)
variable {K:Sponsor G}{T:Seasons K}{V:Z→ℝ}(A:(j:Z)→Alps K T i (V j))
variable (P:(i:Z)→ Libra.Keys G (I i) → G.Color) (h':∀ i, BudY e b k (p i) (P i))
variable (h:∀ j:G.ColorIndex,∀ i:Phase,Tonic Γ g (fun i=>(Phone G).coord j ∘ P i) (k+i.val)) (hΓ:RateLE g Γ V 0)
include h h' hΓ
lemma DawnY {q:Clip}(he:∀ j:Z,(A j).clip=q)(hv:0  ≤  V): Usher Γ g (fun i=>School e b A i (p i) (P i) k) (k+1) m:=by
       let K0(i:Z)(n:Side)(x:Site n):=Pawn.mold (Dune (A i) (n:=n)) 2; let K1(i:Z)(n:Side)(x:Site n):=Pawn.mold (Rh (A i) (n:=n)) 0
       let Zm(j:G.ColorIndex)(i:Z):=(Phone G).coord j ∘ P i
       have hQ(j i): ContDiffAt ℝ ω (Zm j i) 0:= (((Phone G).coord j).toContinuousLinearMap.contDiff.contDiffAt.comp _ (h' i).sm)
       let v(j)(i:Z)(n:Side)(x:Site n):= Pawn.mold (Zm j i ∘ dip (p i) n x) k
       let Q(j:G.ColorIndex)(i:Z)(n:Side)(x:Site n):= LoopM (sett n x e) (Phone G j) b (K0 i n x) (K1 i n x) (v j i n x)
       rw [show (fun i=>School e b A i (p i) (P i) k)=∑ j,Q j from funext fun i=>funext fun n=>funext fun x=>(by unfold School Cake; rw[Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]; rfl)]
       apply Usher.sumX hx; intro j _
       let u:=Phone G j
       let X(i:Z)(n:Side)(x:Site n):= Topper (sett n x e) u b (K0 i n x+K1 i n x)
       let Y(i:Z)(n:Side)(x:Site n):= Topper (sett n x e) u b (v j i n x)
       have hY:Usher Γ g Y k m:=by
            refine Usher.Tug (A:=v j) hx _ _ fun l=>?_ ; intro i; fin_cases i<;> first|exact Pride p (Zm j) hx hK (hQ j) (h j 0) e l | exact Pride p (Zm j) hx hK (hQ j) (h j 1) e l|exact Pride p (Zm j) hx hK (hQ j) (h j 2) e l
       have hX:Usher Γ g X 1 m:= by
            refine Usher.Tug (A:=K0+K1) hx _ _ fun l=>?_ ; let x(i:Z)(n:Side)(x:Site n):= Pry (functorE x e l) (K0 i n x); let z(i:Z)(n:Side)(x:Site n):= Pry (functorE x e l) (K1 i n x); rw [show (fun i n x=>Pry (functorE x e l) ((K0+K1) i n x))=_ from (show _= x+z from funext fun i=>funext fun n=>funext fun x=>pryAdd _ _ _ (tallJ _ _) (tallJ _ _))]; apply Usher.adds hx
            · intro q; exact Gusto.importK hx (RateLE.const _ hx) (readyK e A l he q)
            intro q; apply Gusto.up (Gusto.importK hx ((RateLE.const 1 hx).add hΓ hx) (readyY e A l hv q)); omega
       have hz:Usher Γ g (v j) k m:= by intro i; fin_cases i <;>first|exact goan p (Zm j) hx hK (hQ j) (h j 0)|exact goan p (Zm j) hx hK (hQ j) (h j 1)|exact goan p (Zm j) hx hK (hQ j) (h j 2)
       exact Usher.less hx (Usher.grown (Usher.product hx hX hz) (Nat.add_comm 1 k|>.le)) (Usher.grown hY (Nat.le_succ k))
end YM.OPE.Variance
