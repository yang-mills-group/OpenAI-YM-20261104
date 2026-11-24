import YM.PertExtension.VaneLimit

/-! Finite-error extraction and inversion of the separated sampling jet matrices
of the free curvature kernel only. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.PertExtension.LatticePT
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Next.Rank.Radian Set Real Metric Lattice Beamer CellsInt Wall Band
open Configuration Air Orb Orbit GaussianScore Function Finset Projection
open scoped ContDiff Topology BigOperators Classical NNReal RealInnerProductSpace
variable {G : Gauge} {q : ℕ+} {n M : ℕ} (d : ℕ)
local notation "reg" => (atTop : Filter ℕ)
variable {x : Points n} (hx : x∈conf n)(i j:Fin n)(u v : ℕ→Cover)

lemma panel_closed t : let H := currentError (G:=G) (q:=q) d hx i j u v t
    (∀ i,shutter (H i)) ∧ ∀ j,shutter (fun i=>H i j):=by
    let r:=magnify q t;let C (p s):=((currentX hx G d).cov (i,p) (j,s)).re
    have hX:=echo_shut (G:=G) (n:=side q t) (side_even q t) (u:=u t) (v:=v t) -- args
    exact ⟨fun _=> (Beamer.signal G).sub_mem (hX.1 _) (show shutter _ from choke d (magnify q _) _ _),fun _=> (Beamer.signal G).sub_mem (hX.2 _) (show shutter _ from chokes d (magnify q _) _ _)⟩

variable (hq:1<q.val)(hne:i≠j)(ha:Adrift (x:=x) (q:=q) i j u v)
include hq hne ha
omit hne hq ha in
private lemma absorb {r:ℝ}(h:0<r)(a b:Degree G)(X:Bridge G):amount r a * amount r b * ‖mourn (gesture a) (gesture b) X‖=‖amount r a * amount r b * mourn (gesture a) (gesture b) X‖ :=by
    rw [amount,amount,norm_mul,norm_mul,Real.norm_of_nonneg (pow_nonneg h.le _), Real.norm_of_nonneg (pow_nonneg h.le _)]
private lemma high_bound (M) : ∃ C>0,∀ᶠ t in reg,∀ a b:Degree G, attends d M a→attends d M b→
    amount (magnify q t) a * amount (magnify q t) b * ‖mourn (gesture a) (gesture b) (currentError (q:=q) d hx i j u v t)‖≤C:= by
  let Mset:=( {p:Degree G//attends d M p})
  letI :Finite Mset:=ctrlFinite_pair ..; letI:= Fintype.ofFinite Mset
  choose C H using fun (x y:Mset) =>show ∃c:ℝ, _ from mismatch_bounded d hx i j hne hq u v ha x.val y.val
  let z (t:ℕ):=currentError (G:=G) (q:=q) d hx i j u v t
  let val t x y:= amount (magnify q t) x * amount (magnify q t) y * (mourn (gesture x) (gesture y) (z t))
  have He(x y:Mset):∀ᶠ t in reg, ‖val t x.val y.val‖≤C x y:=H x y
  refine ⟨1+∑ x,∑ y,|C x y|,by positivity, (eventually_all.mpr (fun a=>eventually_all.mpr (He a))).mono fun t ht a b ha hb=>?_⟩
  rw [absorb (by unfold magnify; positivity)]
  let f:Mset:=⟨a,ha⟩;let g:Mset:=⟨b,hb⟩
  exact (ht f g).trans <| (le_abs_self _).trans <| (single_le_sum (s:=Finset.univ) (f:=fun b=>|C f b|) (fun _ _=>abs_nonneg _ ) (mem_univ g)).trans <| (single_le_sum (s:=Finset.univ) (f:=fun a=>∑ b, |C a b|) (fun i _=>sum_nonneg fun _ _=>abs_nonneg _) (mem_univ f)).trans (by linarith)

theorem vane_extract (M): ∃ C>0,∀ η>0,∀ᶠ t in reg,Vane G d (magnify q t) C η M (currentError (q:=q) d hx i j u v t):=by
   obtain ⟨C,hC,h⟩:=high_bound d hx i j u v hq hne ha M -- args order
   refine ⟨C,hC,fun η hη=>?_⟩
   let r t:=magnify q t;let X (t:ℕ):=currentError (G:=G) (q:=q) d hx i j u v t
   suffices hw: ∀ a b:Hub G d 0, ∀ᶠ t in reg, amount (r t) a.val* amount (r t) b.val * ‖mourn (gesture a.val) (gesture b.val) (X t)‖ ≤ η by
       filter_upwards [h,eventually_all.mpr (fun a=>eventually_all.mpr (hw a))] with t hm ht
       exact ⟨(panel_closed d hx i j u v (q:=q) t).1,(panel_closed d hx i j u v (q:=q) t).2,hm,ht⟩
   intro a b; have h:= mismatch_limit d hx i j hne hq u v ha a b; filter_upwards [(h.norm.eventually ((by simpa only [norm_zero] using ge_mem_nhds hη)))] with t ht
   change ‖amount (r t) a.val * amount (r t) b.val * mourn (gesture _) (gesture _) (X t)‖ ≤ η at ht
   exact le_trans (le_of_eq (absorb (show 0<r t by unfold r magnify; positivity) a.val b.val (X t))) ht

variable {S : Type*} (f:S→Address G)
def scopedValue (Xt:ℕ) (a b: KeyIn G d ⊕ S) : ℝ:=mourn (passcode f (magnify q Xt) d a) (passcode f (magnify q Xt) d b) (currentError (q:=q) d hx i j u v Xt)


lemma low_fee (a b) : let E (t) := scopedValue (q:=q) d hx i j u v f t (.inl a) (.inl b)
   Tendsto E reg (𝓝 (0:ℝ)):=by
   intro E; apply (tendsto_zero_iff_norm_tendsto_zero.mpr ?_); refine (tendsto_order.mpr ⟨fun a ha=>Eventually.of_forall fun _=>ha.trans_le (norm_nonneg _),fun ε he=> ?_⟩)
   obtain ⟨C,hC,H⟩:=vane_extract d hx i j u v hq hne ha 1
   obtain ⟨B,hB,b⟩:=sense G d
   have hZ : 0<2*B*B:=by positivity
   specialize H (ε/(2*B*B)) (by positivity); exact H.mono fun t ht=> lt_of_le_of_lt (starbound f ht (one_le_pow₀ (mod_cast hq.le)) (by positivity) (by positivity) b _ _) (by field_simp; nlinarith [hZ])
end YM.PertExtension.LatticePT
