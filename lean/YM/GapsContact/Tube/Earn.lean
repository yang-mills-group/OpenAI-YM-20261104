import YM.GapsContact.SlabCheckpoint
import YM.GapsContact.Tube.Ascent

/-! # Global full tube bounds at scaled logarithmic costs, any Aurora over these contours -/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Tunnel
open Function Set Filter Analysis Distribution Boundary Spec Ascent Trace Trace.Pilot
open MeasureTheory Next.BOUNDARY Org EveryPhase Ascent.Survey Surface
open scoped Topology BigOperators InnerProductSpace NNReal Classical
universe u
variable {n : ℕ}

-- Absolute positions, tests CONSECUTIVE gaps. Handles n zero or one
-- directly. Tolerance δ independent of arity, real joint space etc.
def Room (u:Points n)(δ:ℝ):Prop:=∀ i j:Fin n,i.val+1=j.val → δ ≤ YM.time (u j-u i)- ‖spatial (u j-u i)‖
lemma Room.up {u:Points n}{δ k:ℝ}(h:Room u δ)(ht:k ≤ δ):Room u k:= fun i j a=>ht.trans (h i j a)
lemma Room.mul {r δ:ℝ}{u:Points n}(h:Room u δ)(hr:0≤r):Room (r • u) (r*δ) :=by
  intro i j hij; have hv:= h i j hij; change r*δ ≤ YM.time (r • _-r • _) - _; simp only [PiLp.smul_apply,←smul_sub,Mink.rest_mul,Mink.clock_mul,norm_smul,Real.norm_of_nonneg hr,←mul_sub]; exact mul_le_mul_of_nonneg_left hv hr
lemma Room.mem {u:Points n}{δ:ℝ}(h:Room u δ)(ht:0<δ):u∈fields n:=by
  simp only [fields, mem_iInter]; intro i j a; exact sub_pos.mp (ht.trans_le (h i j a))
lemma Room.of_fields {u:Points n}(h:u∈fields n) : ∀ᶠ δ:ℝ in trail,Room u δ:=by
  unfold Room; simp only [fields,mem_iInter,Mink.inside,Set.mem_setOf_eq] at h; simp only [eventually_all]; intro i j hij; exact (ge_mem_nhds (sub_pos.mpr (h i j hij))).filter_mono nhdsWithin_le_nhds
lemma Room.shore {u:Points n} {δ:ℝ}(h:Room u δ):u-dawn (δ • rate n)∈shores n:=by
  simp only [shores,Set.mem_iInter]; intro i j hij
  have h₁:=h i j hij; simp [sub_eq_add_neg] at h₁
  change ‖spatial _‖ ≤ YM.time _; have hi : (i.val:ℝ)+1=j.val:=by exact_mod_cast hij
  simp [sub_eq_add_neg,Mink.rest_add,Mink.clock_add,Mink.rest_neg,Mink.clock_neg,dawn,Boundary.place,rate,← hi]; nlinarith
lemma Room.of_broad {y:Heights n}{δ:ℝ}(hy:broad y δ):Room (dawn y) δ:=by
  intro i j hij
  simpa [sub_eq_add_neg,dawn,Boundary.place] using hy i j (show i<j by omega)
@[simp] lemma Room.dawn_mul (r:ℝ)(y:Heights n):dawn (r • y)=r • dawn y:=by
  ext1 i; apply Mink.ext_by <;> simp [dawn,Boundary.place,smul_eq_mul]

lemma swell {x:Points n}{r:ℝ}(h:x∈fields n)(hr:0<r) : r • x∈fields n:=by
  obtain ⟨k,hk,ht⟩:= ((Room.of_fields h).and (show ∀ᶠ δ:ℝ in trail,0<δ from self_mem_nhdsWithin)).exists; exact (hk.mul hr.le).mem (mul_pos hr ht)
-- ON ALL COMPACTA eventually have a single clearance lower bound
lemma Room.compact {K:Set (Full n)}(h:IsCompact K)(hk:K⊆tube n):∀ᶠ δ:ℝ in trail,∀ x∈K,Room (shade x) δ:=by
  unfold Room
  by_cases ht: K.Nonempty
  swap
  · simp [Set.not_nonempty_iff_eq_empty.mp ht]
  have hx:∀ᶠ δ:ℝ in trail, ∀ i j:Fin n,i.val+1=j.val→∀ x∈K,δ ≤ YM.time (shade x j-shade x i)- ‖spatial (shade x j-shade x i)‖:=by
    simp only [eventually_all]; intro i j hi
    let d(x:Full n):= YM.time (shade x j-shade x i)- ‖spatial (shade x j-shade x i)‖
    obtain ⟨x,he,hh⟩:= h.exists_isMinOn ht ((show Continuous d from by unfold d;fun_prop).continuousOn)
    have hy:shade x∈fields n:=hk he
    simp only [fields,mem_iInter] at hy; have hg:0 < d x:=sub_pos.mpr (hy i j hi)
    filter_upwards [(ge_mem_nhds hg).filter_mono nhdsWithin_le_nhds] with δ hδ y hy using hδ.trans (hh hy)
  exact hx.mono fun _ hs x hx i j hij=> hs i j hij x hx

variable {G : Gauge} {C : Family G} {S : Table C.book}{f : Extraction.Order}
variable {F: Final C f S} {hG:G.Simple} {L:Almanac F}
variable (L) (i: Survey F) {D:∀ n, Blanket n}
local notation "V" => chamber L i
local notation "B" => Survey.reads L i
local notation "W" => Contour.world (Survey.reads L i)

lemma observed : ∃ Y:Show.Rhythm (C:=C) S V (spread L i), Y.lift=(B).waves ∧ Show.Lights S F.action.spin Y W:=by
  obtain ⟨Y,hY,h⟩:= (Survey.fits L i).reveals; exact ⟨Y,hY,(h F.action.J F.realization.qt.induced).1.I⟩
variable (X:(Survey.reads L i).world.Aurora D)
lemma observe : Bid.cones W ∧ X.FullBody (B).waves :=by
  obtain ⟨Y,hY,h⟩:= observed L i
  rw [← hY]; exact ⟨spectra h,(neon_any h X).2⟩
open Work.C03 in
lemma enough_fields {d:Fin n→ℕ}(v:∀ i:Fin n,S.Field (d i)) {r δ:ℝ}(hr: r∈Ioc (0:ℝ) 1) (hd:δ∈Ioc (0:ℝ) 1)
    {A R:Fin n→ℝ} {m:Fin n→ℕ}
    (h:∀ i,OpenSky F (d i) (R i) (A i) (m i))(hu:∀ i,r ≤ R i) (z: Full n)(hz:Room (shade z) (r*δ)):
    ‖X.emit (fun j=> S.pin _ (v j)) z‖ ≤ ∏ j,(A j^2 *(8 *(LogV r / δ))^(2*m j) * Ascent.cost F (d j) r (v j)):=by
  let k:=r*δ
  obtain ⟨X',he,I⟩:=observed L i
  obtain ⟨hs,hF⟩:= observe L i X
  have hk : k∈Ioc (0:ℝ) 1:= ⟨mul_pos hr.1 hd.1, (mul_le_of_le_one_right hr.1.le hd.2).trans hr.2⟩
  rw [← valley z]; let y:= k • rate n; have hy:y∈east n:=by simpa [y] using dawns (light _) hk.1
  apply upper_tube X _ (hs ..) (hF.hol n _) (etched hy) hz.shore ?_
  -- pure bound
  intro t; rw [hF.pure n _ t y hy,← he]; let p:=Small.logD k
  have ht : broad y k:=by simpa [y] using begins (light n) k hk.1.le
  have hp : Small.enough y p:= enough_logD hk ht
  have h₁: Small.lit (shift t y) p :=by simpa [Small.lit,shift] using hp
  let w:=fun j => S.pin _ (v j)
  rw [Waves.restricted, X'.yields n _ (lit_strict h₁) p h₁]
  apply le_trans (norm_matrix X'.bits p w (shift t y) (Boundary.trace t) h₁)
  have hΩ : ‖(V).omega‖=1:= OS.nil_norm _ (Survey.pantry L i).adopted.laws
  rw [hΩ,mul_one,one_mul]; apply Finset.prod_le_prod (fun _ _=> norm_nonneg _); intro j _
  have hv:δ/8∈Ioc (0:ℝ) 1:= ⟨div_pos hd.1 (by norm_num),by linarith [hd.2]⟩
  have h₂:LogV r / (δ/8)=8*(LogV r / δ):=by ring
  rw [← h₂]; apply (h j).radius L i X'.bits X'.linked r ⟨hr.1,hu j⟩ _ hv p hp.1
  rw [show (p:ℝ)=k/8 from coe_logD hk, mul_div_assoc']

-- expanded version once `Measured` receipts fit a frame/coupling scheme
-- NOT conditional on tube estimates
variable {L} (H:Roll.{u} F hG L)
include H in
lemma full_price {d:Fin n→ℕ}(v: ∀ i: Fin n, ℝ→ S.Field (d i)) (hv:∀ i,Measured F (d i) (v i)):
    ∃ A:ℝ,0≤A ∧ ∃ m:ℕ,∀ᶠ r in trail,∀ (i:Survey F) (D:∀ n, Blanket n) (X:(Survey.reads L i).world.Aurora D),
      ∀ δ∈ Ioc (0:ℝ) 1,∀ z:Full n,Room (shade z) (r*δ) → ‖X.emit (fun j=>S.pin _ (v j r)) z‖ ≤ A* LogV r^m *δ⁻¹^m := by
  choose R A m hR hA hg using fun i=> H.slabs (d i)
  choose b hb hm using hv
  let K(j:Fin n):= A j^2*8^(2*m j)*b j
  refine ⟨∏ j,K j, Finset.prod_nonneg (fun j _=> by have hx:=hb j; unfold K; positivity), ∑ j,2*m j,?_⟩
  have hT:∀ j:Fin n,∀ᶠ r in trail,r≤R j:=fun j=> (ge_mem_nhds (hR j)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_all.mpr hT, eventually_all.mpr hm,self_mem_nhdsWithin,(ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds] with r ht hr h₁ h₂ i D X δ hd z hz
  have he: r∈ Ioc (0:ℝ) 1 := ⟨h₁,h₂⟩
  let M:=∑ j, 2*m j
  refine (enough_fields L i X (fun j=> v j r) he hd hg ht z hz).trans ?_
  calc
     _ ≤ ∏ j,(A j^2*(8*(LogV r/δ))^(2*m j)*b j):=by
        apply Finset.prod_le_prod (fun j _=> ?_) (fun j _=> mul_le_mul_of_nonneg_left (hr j) ?_)
        · rw [pow_mul]; unfold Ascent.cost; positivity
        rw [pow_mul]; positivity
     _ = ∏ j,(K j*(LogV r / δ)^(2*m j)):=by simp [K, mul_pow,mul_comm,mul_assoc]
     _ = _:=by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, div_eq_mul_inv,mul_pow,mul_assoc]
end YM.GapsContact.Tunnel
