import YM.MS.Hem.Asti
/-!
# Preserving relevant subspaces at continued resolution

Will: closed linear test, on all symbol stencils. No angular projections in f_z.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff Interval
variable {I E:Type} {G:Gauge} {W S: Mob G} {x:ℂ} {b:Bool} {n m j:ℕ} {r k:ℤ}
abbrev LeanR (G:Gauge):= Submodule ℝ (Mob G)
abbrev LeanC (G:Gauge):= Submodule ℂ (Mob G)
structure Will (P: LeanR G): Prop where
    touch: Fall (· ∈ (P:Set (Mob G)))
    walk (x:Mob G) (s:ℝ): x ∈ P→ plow 0 s x∈ P
    runner (u:ℝ→Mob G)(t:ℝ): Gather u t → (∀ i,u i∈P)→ mend u t∈ P
lemma Will.inter (P Q:LeanR G)(hp: Will P)(hq:Will Q): Will (P⊓Q):= by
    constructor; · intro I L _ f F H he; exact ⟨hp.touch H (he.mono fun i he=>he.1), hq.touch H (he.mono fun i he=>he.2)⟩
    · intro x s hu; exact ⟨hp.walk x s hu.1,hq.walk x s hu.2⟩
    intro u t hT H; exact ⟨hp.runner u t hT fun i=>(H i).1, hq.runner u t hT fun i=> (H i).2⟩
variable {P: LeanR G}{Q:LeanC G}
lemma Will.soft (h:Will P)(hr:W∈P){x:ℂ}(he:star x=x)(t:ℝ): plow x t W∈P:= by
   obtain ⟨r,rfl⟩:=Complex.conj_eq_iff_real.mp he; obtain ht := shift (0:ℂ) r t W; rw [zero_add,amount_mint] at ht; rw [ht,show ((rexp (r*t):ℝ):ℂ)= rexp (r*t) • (1:ℂ) by simp [Complex.real_smul],smul_one_smul]; exact P.smul_mem _ (h.walk W t hr)
lemma Will.seo (h:Will (Q.restrictScalars ℝ))(he:W∈Q)(x:ℂ)(t:ℝ): plow x t W∈ Q:= by obtain hp:= shift (0:ℂ) x t W; rw [zero_add] at hp; rw [hp]; exact Q.smul_mem _ (h.walk W t he)
lemma Will.jet (h:Will P)(ht:W∈P)(hp:kPrice W)(j:ℕ): Tad W j∈P:= by
    induction j using Nat.strong_induction_on with
    | h j ih=> exact h.touch (ray_white hp j) (Eventually.of_forall fun i=> show wood j (-(j:ℂ)) i W∈P from h.soft (P.sub_mem ht (P.sum_mem fun v hv=> ih v (Finset.mem_range.mp hv))) (by simp) i)
lemma Will.mist (h:Will P)(ht: W∈P)(hp:kPrice W)(j:ℕ): Hem.clear j W∈ P:= P.sub_mem ht ( P.sum_mem fun i _=> h.jet ht hp i)
lemma Will.light (h:Will P)(ht:W∈P)(he:star x=x)(hp:kPrice W)(hb:0<x.re+n): progress n x W∈P:= h.runner _ _ (frame hp hb _) (fun i=>h.soft (h.mist ht hp n) he i) -- strange k Int; fix
lemma Will.lamp (h:Will (Q.restrictScalars ℝ))(ht:W∈ Q)(hp:kPrice W)(hb:0<x.re+n): progress n x W∈ Q:= h.runner _ _ (frame hp hb _) (fun i=> h.seo (h.mist ht hp n) x i)
-- canned

def sturdy (b:Bool)(G:Gauge): LeanC G where
   carrier:= Sturdy b
   add_mem':=Sturdy_plus
   zero_mem':= Sturdy0
   smul_mem' c _ h:= Sturdy_scale h c
def collar (i:ℤ)(G:Gauge): LeanC G where
   carrier:= Collar i
   add_mem' (h:Collar i _) (he:Collar i _):= ⟨fun m=>(h.sym m).add (he.sym m), fun m g=> by simp only [Pi.add_apply,map_add,h.color m g,he.color m g], fun m=> (h.ghost m).add (he.ghost m)⟩
   zero_mem':=⟨fun _=>Symm.zero,fun _ _=>map_zero _,fun _=> Rails.zero⟩ -- type Def
   smul_mem' z _ h := ⟨fun m=>(h.sym m).smul z, fun m g=> by simp only [Pi.smul_apply, map_smul,(show Collar i _ from h).color m g], fun m=> (h.ghost m).smul z⟩
def good (i:ℤ)(G:Gauge): LeanC G where
   carrier:= Goods i
   add_mem' h he := fun m=> (h m).add (he m)
   zero_mem' := fun _=> Rails.zero
   smul_mem' c _ h :=fun m=> (h m).smul c
def grade (i:ℤ)(G:Gauge): LeanC G where
   carrier:= Issue i
   add_mem' h he:=fun m=>Book.Limit.add (h m) (he m)
   zero_mem':= fun _ _ _=>rfl
   smul_mem' c _ h:= fun m=>Book.Limit.smul c (h m)
def sight (G:Gauge): LeanR G where
   carrier:= Sight
   add_mem' {x y} h g:= fun m i=>by simp only [Pi.add_apply, (h m i),(g m i),star_add]
   zero_mem':= fun _ _=> (star_zero _).symm
   smul_mem' c _ h:= fun m i=>by simp only [Pi.smul_apply,Complex.real_smul,h m i,star_mul']; simp -- look order
end YM.MS.Hem.Mell
