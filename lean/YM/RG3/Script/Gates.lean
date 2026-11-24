import YM.RG3.Script.Stable
/-! # All support & projection surcharges for short script on native torus.
Uniform after callers secure radii to pay these post-L/per-stage constants.
Can instead buy tails on their own longer connectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Estate Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {V:Type*} [DecidableEq V]{R:Census V}{ζ:V→Site n}{G:Gauge}
  {e : Edition ζ R G} {A : Estate n R}{p : BudgetPoint}
namespace Edition

def tollGate (a:ℝ) (D:ℕ):ℝ := Real.exp (a*((D+D+1:ℕ)^4:ℕ))
lemma moved_to (ι : Type*) (q : ι→R.Mode)(f:ι→ℝ)(w:V→ℝ)
    (hf : ∀ i,0≤f i)(hw : ∀ v,0<w v) {a b : ℝ}(ha:0≤a)(H:ι→ℕ)(D:ℕ)
    (hA: ∀ i, A.radius (H i) ≤ D*p.B)
    (h:∀ v,SumBudget (fun i=> if v∈(q i).val then Poly.toll w (q i)*f i else 0) b) v:
    SumBudget (per p.B a w q (A.region ∘ H) f v) (tollGate a D*b):=by
  let T:=tollGate a D; have ht : 0 ≤ T:=(Real.exp_pos _).le
  refine budget_mono (budget_scale ht (h v)) (fun i=>per_nn (fun _=>(hw _).le) hf _ _) (fun i=>?_)
  unfold per expense
  split
  next hr=>
    have he:coverNumber p.B (A.region (H i)) ≤ (D+D+1)^4:=by
      apply (Corona.cover_mono _ p.B).trans (Corona.tile (A.post (H i)) D p.B p.B_pos)
      exact Corona.halo_mono (hA i) (Finset.Subset.refl _)
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone (show _ ≤ a*↑((D+D+1:ℕ)^4) from mul_le_mul_of_nonneg_left (by exact_mod_cast he) ha)) (hf _)) (Poly.worth hw _).le).trans_eq (by unfold tollGate; ring)
  simp

variable {c:Crew V}(s:e.Size c A)

def regroup (e:Edition ζ R G)(f : ℕ→ℝ) : Reg V→ℝ:=Sum.elim f (Sum.elim (fun i=>‖e.footer.value i‖) (fun i=> ‖e.pure i‖))
lemma nondestructive {f:ℕ→ℝ}(hf : ∀ i,0≤f i) (i): 0 ≤ regroup e f i:=by rcases i with i|(i|i) <;> first |exact hf _| exact norm_nonneg _
lemma minor_subtype {α:Type*}(s:Set α){f:α→ℝ}{C:ℝ}(h:SumBudget f C):SumBudget (fun i:s=> f i.val) C:= by
  refine budget_of_sum (fun _=> h.1 _) fun z=>le_trans ?_ (budget_sum h (z.image Subtype.val))
  erw [Finset.sum_image]; exact fun _ _ _ _ h=>Subtype.val_injective h

-- before editing, can buy compact-model movement from CURRENT p
-- credentials plus hull costs (both endpoints included), independent of
-- Fintype.card V but θ already in h. No additional reserve on d.contents
-- regular needed for movements wholly fitting compact hull. All unedited
-- and error H for further projection still need their stage reserves.
lemma oxygen {u v Y a b: ℝ}{w:V→ℝ}{f:ℕ→ℝ}(hw:∀i,0<w i)(h:e.Principle p)(hF:e.Grant p w a u v Y f)(ha:0≤a) (hb:0≤b)
    (D:ℕ)(hs:∀ i:Public c,A.radius (s.item i) ≤ D*p.B):
    (cutting s).Strap w p b (tollGate b D * (v+(Y+u))) (fun i=>regroup e f i.val):=by
  let F:=cutting s
  refine ⟨fun i=>nondestructive hF.nn _,fun i U=>?_, fun i=> ?_⟩
  · rcases i with ⟨i|(i|i),hi⟩
    · obtain ⟨x,hx⟩:=h.hot i
      change ‖masked p.threshold (e.home i) (e.song i) U‖ ≤ _
      by_cases hh:Healthy p.threshold (e.home i) U
      · rw [masked_eq _ _ _ _ hh]; exact (hF.pay i x hx).2 U hh [] (by simp) (by simp)
      rw [masked_ne _ _ _ _ hh,norm_zero]; exact hF.nn i
    · exact le_rfl
    exact le_rfl
  apply moved_to (p:=p) _ _ _ _ (fun i=>nondestructive (e:=e) hF.nn i.val) hw hb _ _ hs
  intro x
  have he:SumBudget (fun i : Reg V=>if x∈(Reg.glyph e i).val then Poly.toll w (Reg.glyph e i)*regroup e f i else 0) (v+(Y+u)):=by
    refine Cost.sum ?_ (Cost.sum ?_ ?_)
    · refine budget_mono (hF.more x) (fun i=>?_ ) (fun i=>?_)
      · split; exact mul_nonneg (Poly.worth hw _).le (hF.nn _); rfl
      simp only [Reg.glyph,Sum.elim_inl,per]; split
      next hl=>
        unfold expense
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hF.nn i) (Real.one_le_exp (by positivity))) (Poly.worth hw _).le
      rfl
    · refine budget_mono (hF.captions x) (fun i=>?_ ) (fun i=>?_)
      · split; exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _); rfl
      simp only [Reg.glyph,Sum.elim_inl,Sum.elim_inr,per,expense]; split
      next hl=>
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp (by positivity))) (Poly.worth hw _).le
      rfl
    let g i:= if x∈(R.fire i).val then Poly.toll w (R.fire i)*‖e.pure i‖ else 0
    have h0:0≤u:= (mul_nonneg (hw x).le (norm_nonneg _)).trans (hF.one _)
    refine budget_of_sum (fun i=>?_ ) (fun i=>?_)
    · split; exact mul_nonneg (Poly.worth hw _).le (norm_nonneg _); rfl
    change (∑ j∈i,g j) ≤ _
    rcases em (x∈i) with h|h
    · rw [Finset.sum_eq_single (s:=i) (f:=g) x (fun j _ hj=>if_neg fun hv=>hj (mem_singleton.mp hv).symm) (fun hx=> (hx h).elim)]
      dsimp [g]; rw [if_pos (show x∈(R.fire x).val from mem_singleton_self _), Poly.solo_toll]; exact hF.one _
    have hf j (hh:j∈i) : g j=0:=if_neg (fun he=> h ((show x=j from mem_singleton.mp he) ▸ hh))
    rw [show (∑ j∈i,g j)=0 from sum_eq_zero hf]; exact h0
  have hx := minor_subtype ({i:Reg V|c.book i=true}:Set _) he
  -- Decidable instances in Reg: compare ITEs proof irrelevance
  change SumBudget (fun j : Public c=> if x∈(A.style (s.item j)).val then _ else _) _
  have hyy : SumBudget (fun i : Public c=> if x∈(Reg.glyph e i.val).val then Poly.toll w (Reg.glyph e i.val)*regroup e f i.val else 0) (v+(Y+u)) := hx
  convert hyy using 1; ext1 i; rw [s.centered i]; rfl
section projection
-- projection for every literal slot in V while all occurrences/captions kept
open RG3.Primary
variable {W : Type} [DecidableEq W] {R': Census W} {ζ': W→ Site n} {e': Edition ζ' R' G}
  {P:Rep G n}{d:Deck R' P}{D:W→ℕ}{X:(s:W)→ Labels.Frame G (D s)}{L:(s:W)→SectionData (X s)}
  {k : W→ℝ}

lemma fundsCanon {a c u Y:ℝ}{w:W→ℝ}{f:ℕ→ℝ}(hH:Hol G)(he:e'.Principle P.p)(ht:e'.Grant P.p w a u c Y f)(hw:∀ i,0<w i)
    (hr:∀ s,Readable hH (L s) P.p n (k s))(ha:0≤a)(K:ℕ)(hK:∀s,coverNumber P.p.B ((L s).footprint (ζ' s)) ≤ K)(C:ℝ)(hC:∀s,atomPrice hH (X s) (k s) ≤ C):
    Loaded hH a f (Real.exp (a*K)*C*c) L d e' k w:=by
  have hF(s): ζ' s ∈ (L s).footprint (ζ' s):= by simpa only [SectionData.footprint,map_zero,zero_add] using mem_image_of_mem (fun x=> wrap n x+ζ' s) (hr s).sound.anchored
  have hc s:= atomPrice_ge_one hH (X s) (hr s|>.nonneg)
  have hp s i (hh:e'.only i s):s∈(e'.pins i).val:=hh ▸ mem_singleton_self _
  refine ⟨fun s i hi=>ht.pay i s (hp s i hi),fun s=>?_⟩
  let M:=Real.exp (a*K)*C
  have hM:0≤M:=mul_nonneg (Real.exp_pos _).le ((zero_le_one.trans (hc s)).trans (hC _))
  refine budget_mono (budget_scale hM (ht.more s)) (fun i=>?_ ) (fun i=>?_)
  · unfold paidR; apply mul_nonneg (hw s).le; apply mul_nonneg (Real.exp_pos _).le
    unfold Primary.ink; split
    · exact mul_nonneg (zero_le_one.trans (hc _)) (ht.nn _)
    exact le_rfl
  let S:=e'.home i; let Z:=(L s).footprint (ζ' s)
  by_cases hh:e'.only i s
  · have hv : ζ' s∈S:=he.rem i s (hp _ _ hh) --yes
    have hZ := (Corona.meets_sum hv (hF s) (P.p.B)).trans (Nat.add_le_add_left (hK s) _)
    have hα : Real.exp (a*coverNumber P.p.B (S∪Z)) ≤ Real.exp (a*coverNumber P.p.B S)*Real.exp (a*K):= by
      rw [← Real.exp_add,←mul_add]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast hZ) ha)
    unfold paidR expense Primary.ink per; rw [if_pos (show Primary.earns s (e'.scribe d) i from hh), if_pos (hp _ _ hh),show e'.pins i= _ from hh,Poly.solo_toll]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul hα (mul_le_mul_of_nonneg_right (hC s) (ht.nn i)) (mul_nonneg (zero_le_one.trans (hc s)) (ht.nn i)) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (hw s).le).trans_eq ?_
    unfold expense S; ring
  unfold paidR expense Primary.ink; rw [if_neg (show ¬Primary.earns s (e'.scribe d) i from hh),mul_zero,mul_zero]
  exact mul_nonneg hM ((ht.more s).1 i)
end projection
end Edition
end YM.RG3.Script
