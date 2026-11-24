import YM.MS.Swirl.Resolute
import YM.FVAAlt2.Center
import YM.FVAAlt2.WickPull

/-!
# Exact position counterpart of PhysicalSum, odd and even parts, BEFORE eliminating ghosts
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Plane MS.Book MS.Native.Paint MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Swirl MS.Swirl.Near MS.Native.Wilsonian
open Finset MS.Puff MS.Puff.Actors MS.Puff.SplitP MS.Puff.Engine MS.Puff.Mom MS.Cylinder MS.Cylinder.Lab MS.Fleet Lattice
open Convolve Program
variable {G:Gauge}{n:Side}{W:Type}[LinearOrder W]

local notation "A0" => Mode G n
local notation "p" => Draft.DotFlip
local notation "F" => fourier G n

def posEnergy (U : ℕ → Dot G Cover) (n:Side)(b:Bool) : SpecB (Mode G n) :=
    fun k=> if k=0 then 0 else pay b • docket n (U k)

def posMark (n:Side)(x:Site n) : Linear (Dot G Cover) (BL (Mode G n)) :=
  (Stack _ _).subtype ∘ₗ (Lab.Shift x) ∘ₗ shown n

def stencil (v: W→ℕ→Dot G Cover) (x : W→Site n) : Mate A0 W := fun s=>
  if h:s.Nonempty then if s.card=1 then pointL ℕ (posMark n (x (s.min' h))) (v (s.min' h)) else 0 else 0

def posCov (G:Gauge)(n:Side)(b:Bool) := pullCov (Master G n b : Matrix _ _ _) (fourier G n)

lemma Energy_equiv (t:Team)(z:ℝ)(b:Bool) : NRG t z n G b = pullSeries F (posEnergy (style G t z) n b):= by
  funext k; unfold NRG; split_ifs with h
  · change 0=pull F (if k=0 then 0 else _); rw [if_pos h,map_zero]
  change _=pull F (if k=0 then 0 else _);rw [if_neg h,send_bulk];rfl

lemma Marks_equiv (V: W → Actor G)(z:ℝ)(A:Cover)(c:W→ Cover) : Marks V z n A c = fun s=> pullSeries F (stencil (fun w=> V w z) (fun w=>wrap n (A+c w)) s):= by
  funext s; unfold Marks stencil; split
  swap; · exact (map_zero _).symm
  rename_i h
  split; next hc=> exact funext (fun i=> (all_mark A _ _).symm)
  exact (map_zero _).symm

lemma docket_fee (F0:Dot G Cover)(hf:Symm p F0.val) {k:ℤ} (h:Limit F0.val k) : docket n F0∈FeeP p := by
  constructor
  · change Symm p (sumHome (shown n F0)).val
    rw [total_uses,sum_stack]; refine Symm.sum _ (fun i _=> ?_)
    have hv: Symm p (shown n F0).val := Tie.sym (ferry_tie (post (wrap n)) (fun i:LightMode G Cover=>rfl)) F0 hf
    exact Tie.sym (ferry_tie (post fun x:Site n=> i+x) (fun _:Mode G n=>rfl)) (shown n F0) hv
  exact minH (limit_sum n h)

lemma Γ_posE (U:ℕ→Dot G Cover)(he:∀ i, Symm p (U i).val)(hl:∀ i,∃ k:ℤ, Limit (U i).val k)(n:Side)(b:Bool): Γ (posEnergy U n b) p:= by
  intro i _; unfold posEnergy; split; exact (FeeP p).zero_mem
  obtain ⟨k,h⟩:= hl i; exact (FeeP p).smul_mem _ (docket_fee (U i) (he i) h)

lemma Γ_posStyle (t:Team)(z:ℝ)(b:Bool): Γ (posEnergy (style G t z) n b) p :=
  Γ_posE _ (fun i=>((core_circle G t).actual i z).symm) (fun i=> ⟨_,style_limit t z G i⟩) n b

lemma pin_fee (x : Site n)(F0:Dot G Cover)(hf:Symm p F0.val) {k:ℤ} (h: Limit F0.val k): posMark n x F0 ∈ FeeP p := by
  have hv: Symm p (shown n F0).val := Tie.sym (ferry_tie (post (wrap n)) (fun i:LightMode G Cover=>rfl)) F0 hf
  constructor
  · exact Tie.sym (ferry_tie (post fun y:Site n=> x+y) (fun _:Mode G n=>rfl)) (shown n F0) hv
  apply minH (v:=k); exact Limit.shades _ (Book.limit_enter n h) (way (post (fun y:Site n=>x+y)))

lemma Γ_stencil (v : W→ℕ→Dot G Cover)(x:W→Site n)(h:∀ w k, Symm p (v w k).val) (he:∀ w k,∃ N:ℤ, Limit (v w k).val N) (s:Finset W): Γ (stencil v x s) p:= by
  unfold stencil; split
  · rename_i H; split; · intro n1 _; obtain ⟨N,hv⟩:= he (s.min' H) n1; exact pin_fee _ _ (h _ _) hv
    exact Submodule.zero_mem _
  exact Submodule.zero_mem _

lemma fontΓ {M:Mate (FixedMode G n) W}{s:Finset W}(hm:∀ s, Γ (M s) p): Γ (Font p M s) p :=
  costCheer (marked W) (S:=PermV p) (refineπ useN (coin 1) feeUnit) (fun _ h _ ht=> ΤΓ_pair h ht) («F»:=M) (fun s _=>hm s) s (Set.mem_univ _)

theorem superEnd (V:W→Actor G)(z:ℝ)(A:Cover)(c:W→Cover)(h:∀ w i,Symm p (V w z i).val)(he:∀ w i,∃ k:ℤ,Limit (V w z i).val k)(s:Finset W)(t:Team)(b:Bool)(X:ℕ→ℂ):
    PhysicalSum G t z n b s c A V X ↔ Endμ (posCov G n b) p (posEnergy (style G (Stripped t) z) n b) (Font p (stencil (fun w=> V w z) (fun w=>wrap n (A+c w))) s) X:= by
  unfold PhysicalSum
  rw [Energy_equiv,Marks_equiv,show Font _ (fun s=>pullSeries F (stencil (fun w=> V w z) (fun w=>wrap n (A+c w)) s)) s= _ from pull_font (fourier_Tie n G) _ s]
  exact end_pull (fourier_Tie n G) (Master G n b) (Γ_posStyle (n:=n) (G:=G) (Stripped t) z b) (fontΓ (Γ_stencil _ _ h he))

end YM.FVAAlt2
