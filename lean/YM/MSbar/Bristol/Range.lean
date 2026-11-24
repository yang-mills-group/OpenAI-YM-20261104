import YM.MSbar.Bristol.Dot
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
open JetTab
variable {p q k m:ℕ} {a b c1 c2 C v w u r:ℝ}{f g:Positions σ→ℝ}{i:σ}{l:σ→Site c}{Q:Set (Positions σ)}
noncomputable def fluxSet (σ:Type)[Fintype σ](m:ℕ)(u:ℝ): Set (Positions σ):= if m<4 then {0} else Metric.closedBall 0 u
local notation "Y"=>View σ
lemma tunes (hp:JetTab l a p v Q f m b)(h:JetTab l a p v Q g m c1)(he: m< k)(hv:0<v)(hf:∀ x∈Q,ContDiffAt ℝ k f x)(hg:∀ x∈Q,ContDiffAt ℝ k g x): JetTab l a p v Q (f+g) m (b+c1):=by
    obtain ⟨hh,P,hF,hP⟩:=hp; obtain ⟨hh',V,hξ,hV⟩:=h; refine ⟨add_nonneg hh hh',fun l=>P l+V l,fun l' hl=>⟨add_nonneg (hF _ hl|>.1) (hξ _ hl|>.1),fun x hx=>?_⟩,fun i=>?_⟩
    · have ht:= Lis.addedL k (l'.map (@bolt σ)) _ _ (hf x hx) (hg x hx) (by rw [List.length_map];omega); unfold buoy; rw [ht]; refine (mul_le_mul_of_nonneg_right (abs_add_le ..) (pow_nonneg hv.le _)).trans ?_; rw [add_mul]; exact add_le_add (hF l' hl|>.2 x hx) (hξ l' hl|>.2 x hx)
    simp_rw [add_mul,pockets]; exact add_le_add (hP i) (hV i)
lemma confl (hp:RangeB l p a v f m b)(hg:RangeB l p a v g m c1)(hh: m< k)(hv:0<v)(hf:∀ x∈Metric.closedBall 0 v,ContDiffAt ℝ k f x)(hG:∀ x∈Metric.closedBall 0 v,ContDiffAt ℝ k g x): RangeB l p a v (f+g) m (b+c1) := by
    constructor; intro i hi; have hx : fluxSet σ i v⊆Metric.closedBall 0 v:=by unfold fluxSet; split; exact Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hv.le); rfl -- rfl goal subset
    exact tunes (hp.1 i hi) (hg.1 i hi) (by omega) hv (fun x he=>hf x (hx he)) (fun x he=>hG x (hx he))
lemma runC (hp:RangeB l p a v f m b)(h:b≤c1): RangeB l p a v f m c1:= ⟨fun i hi=> JetTab.cast (hp.1 i hi) h Set.Subset.rfl⟩
local notation "P"=> Pot σ
variable (p':Pot σ)
lemma colorR (he:p'.totalDegree≤ m+1)(hv: Tin l a p m v p' b)(hr:0<v)(ha:0≤a): RangeB l p a v (clue p') m ((m+1:ℕ)*b):=by
    have hp:0≤b:=hv.1; constructor; intro j hj; let E(j):= JetTab l a p v (Metric.closedBall 0 v) (clue p') j; let I(j:ℕ):=((m-j:ℕ):ℝ)*b+b; have he':E (m+1) 0:=by
        refine ⟨le_rfl,fun _=> 0,fun i hi=>⟨le_rfl,fun x h=>?_⟩,fun i=>?_⟩
        · rw [CrossH.tours,Bakery.blank_list,abs_zero,zero_mul];omega
        simp only [zero_mul]; exact (spool (ι:=σ) (m+1)).le
    have h(j:ℕ)(hp:j ≤ m) : JetTab l a p v {0} (clue p') j b:=(pressed _ _ _ _ _ _ _ hr).mpr ⟨hv.dec,hv.fan j hp⟩ -- arguments
    have hi(j:ℕ)(hk:j≤ m):E j (I j):=by induction hk using Nat.decreasingInduction with
        | self=> unfold I; rw [Nat.sub_self,Nat.cast_zero,zero_mul,zero_add]; apply JetTab.cast (JetTab.plume he' (h m le_rfl) hr ha (le_rfl : m+2 ≤ m+2) (fun x _=> (helm ..).contDiffAt)) (by rw [zero_add]) Set.Subset.rfl
        | of_succ j hh ih=> apply JetTab.cast (JetTab.plume ih (h j hh.le) hr ha (le_rfl : j+2 ≤ j+2) (fun x _=>(helm ..).contDiffAt)) _ Set.Subset.rfl; unfold I; rw [show m-j=m-(j+1)+1 by omega,Nat.cast_add_one]; apply le_of_eq; ring
    apply JetTab.cast (hi j hj); unfold I; push_cast; linarith only [mul_le_mul_of_nonneg_right (show ((m-j:ℕ):ℝ) ≤ (m:ℝ) by exact_mod_cast Nat.sub_le m j) hp]
    split; exact Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hr.le); exact Set.Subset.rfl
lemma flex (hv:0<v)(hp:JetTab l a p v Q f m b)(he:m+1 ≤ k)(hf:∀ x∈Q,ContDiffAt ℝ k f x): JetTab l a p v Q (r • f) m (|r| *b):=by -- variable r
    obtain ⟨hh,g,hg,hQ⟩:=hp; refine ⟨mul_nonneg (abs_nonneg _) hh,fun i=>|r| *g i,fun L he' =>⟨mul_nonneg (abs_nonneg _) (hg _ he'|>.1),fun x hx=>?_⟩,fun i=>?_⟩
    · unfold buoy; change |roc (fun x=>r*f x) (L.map (@bolt σ)) x| * _ ≤ _; rw [show roc _ _ _= _ from Lis.wed k (L.map (@bolt σ)) r f (hf x hx) (by rw [List.length_map];omega),abs_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hg _ he'|>.2 x hx) (abs_nonneg _)
    simp_rw [mul_assoc,sheen]; exact mul_le_mul_of_nonneg_left (hQ i) (abs_nonneg _)
lemma srep (p': ℝ)(h:RangeB l p a v f m b)(he:m < k)(hf:∀ x∈Metric.closedBall 0 v,ContDiffAt ℝ k f x)(hv:0<v): RangeB l p a v (p' • f) m (|p'| *b):=by
      refine ⟨fun i hi=>flex hv (h.peak i hi) (by omega) (fun j hj=>hf _ ?_)⟩; split at hj; next hp=> rw [Set.mem_singleton_iff.mp hj]; exact Metric.mem_closedBall_self hv.le
      exact hj
local notation "X"=>Positions (Primary c G)
local notation "V"=>Primary c G
lemma stroll {f:X→ℝ}{l:V→ Site c}(he:RangeB l p a v f m b)(hh:m<k)(hv:0<v)(hf:∀ x∈ Metric.closedBall 0 v,ContDiffAt ℝ k f x)(hW:0<w)(hu:0<u)(hp:u*w≤ v): RangeB l p a w (f∘ Yturn u) m b:=by
     let T:= Metric.closedBall (0:X) v; let W(i:ℕ) := fluxSet (Primary c G) i w; let L : X→L[ℝ] X:= Yturn u
     have hw(i:ℕ) : W i⊆Metric.closedBall 0 w:=by unfold W fluxSet; split; exact Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hW.le);rfl
     have hL(i:ℕ)(x:X)(hx:x∈W i):L x∈T:=by
          rw [mem_closedBall_zero_iff]; change ‖u • x‖≤v; rw [norm_smul,Real.norm_of_nonneg hu.le]; exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp (hw i hx)) hu.le).trans hp
     constructor; intro i hi; obtain ⟨hr,g,hg,hG⟩:= he.1 i hi; refine ⟨hr,g,fun L' h'=>⟨(hg _ h').1,fun x hx=>?_⟩,hG⟩; have he:buoy (f ∘ L) x L'= u^(i+1)*buoy f (L x) L':=by -- syntax
          have hf':ContDiffAt ℝ k f (L x):=hf _ (hL _ _ hx); rw [chain _ _ k x (hf'.comp x L.contDiff.contDiffAt) (by omega), chain _ _ k _ hf' (by omega)]; change iteratedFDeriv _ _ _ _ _=_; let U(j:Fin L'.length):=bolt (L'.get j); rw [iter_lin_at (hf'.of_le (show (L'.length:ℕ∞ω) ≤ k by exact_mod_cast (by omega : L'.length ≤ k))), ContinuousMultilinearMap.compContinuousLinearMap_apply]; change iteratedFDeriv ℝ _ f _ (fun i:Fin L'.length=>u • U i)= _; rw [(iteratedFDeriv ℝ L'.length f (L x)).map_smul_univ (fun _=>u) U,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rw [← h']; rfl -- fix
     rw [show f ∘ _ = f ∘ L from rfl, he,abs_mul,abs_of_nonneg (pow_nonneg hu.le _)]; apply le_trans _ (hg L' h'|>.2 (L x) ?_); swap
     · have hv : x∈ W i:=hx; by_cases he:i<4; swap; · rw [if_neg he]; exact hL i x hv
       rw [if_pos he] at hx ⊢; rw [Set.mem_singleton_iff.mp hx]; exact Set.mem_singleton_iff.mpr (map_zero _)
     calc
         _ = |buoy f (L x) L'| *(u*w)^(i+1) :=by ring
         _ ≤ _:= mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hu.le hW.le) hp _) (abs_nonneg _)
end YM.MSbar.Bristol
