import YM.RG17.Temple
/-! Physical payment all home and all ranks.
    still bridge needed between `paid` maps of the SHORT coarse spot to
 predictions in L.frame ledger. Consumer concrete (cf Slate.repay). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set Spec MeasureTheory OPE OPE.Orbits SharpGram Trace Next.UVStress PhysicalNext PhysicalNext.Repeat.Legato Lattice RG Wilson
open Extra.Multi FullVolume.Sever Marker Source Overlay PhysicalNext.Repeat.Mallow Bandage MergeProof MergeProof.Accent Ribbons ManyCopies Extra.Histories Extraction Word Next.Rank Station Edition Spindle Cells
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f: Extraction.Order}{F: Spec.Final R.family f S}{B:Filter (ℕ×ℕ)}{L:Layout F} {D:Lenses.Mantle F B}{s:Extraction.Sequence}
    (Z:Ledger L)(fx:Flick R.family.path.levels)(W:Services R.family f S)
set_option quotPrecheck false
local notation "C"=> R.family
local notation "ι"=> R.family.path.levels
local notation "H"=> R.family.path.levels.clock.hatBeta
local notation "Q"=> wheel R.family
local notation "a"=> R.family.S.a
local notation "δ"=> renal R.family.path.levels
local notation "η"=> near R.family.path.levels
variable {n:ℕ} (J:Fin n) (d:Fin n→ℕ) (t l:ℕ) {α:ℝ} (Y m:ℝ→ℕ)
local notation "S'"=> R.family.path.levels.budget
local notation "e'"=> -((t+1/16:ℝ)*(1-α))
local notation "T"=> OPE.run

-- current regulator; compare at earlier mesh
open Push
variable {WLG:Bid.Worth} {rL:ℕ→ℕ} {doors} (g: Log.LogPackage R.family WLG rL doors)
open OPE.Log

abbrev Paintbrush (R:Run G) {S:Table R.family.book}{f:Extraction.Order}{F:Spec.Final R.family f S}(L:Layout F) (d:Fin n→ℕ) (t:ℕ)(r:ℝ)(x m:ℕ)(e:ℝ) (b:Fin n→ Cover)(u:(i:Fin n)→R.family.label (d i))(j:ℕ×ℕ) (z:R.family.label t):Prop:= Temple R d t r j.1 j.2 (pathTag R d r b j) (fun i=>atRef L _ r j (u i)) (e/2) x m z
variable {r:ℝ} (b:ℝ→Fin n→ Cover)
lemma scenesT (k l i₀:ℕ)(hp:R.family.ref t ≤ l)(u:(j:Fin n)→R.family.label (d j)) (q v:ℝ) (he:∀ᶠ i in L.lens,∃ z, readingPrice R d L r k l q v t (b r) u i z ∧ Paintbrush R L d t r i₀ l q (b r) u i z): ∃ (y:ℕ×ℕ→R.family.label t) (M:R.family.label t) (p:Filter (ℕ×ℕ)), p.NeBot ∧ p≤L.lens∧ Tendsto y p (𝓝 M)∧ ∀ᶠ j in p, readingPrice R d L r k l q v t (b r) u j (y j) ∧ Paintbrush R L d t r i₀ l q (b r) u j (y j):=by
    letI:= L.notbot
    let y i:= if hy:∃ z, readingPrice R d L r k l q v t (b r) u i z ∧ Paintbrush R L d t r i₀ l q (b r) u i z then hy.choose else 0
    have he:∀ᶠ i in L.lens, readingPrice R d L r k l q v t (b r) u i (y i) ∧ Paintbrush R L d t r i₀ l q (b r) u i (y i):=he.mono fun i h=>by unfold y; rw [dif_pos h]; exact h.choose_spec
    obtain ⟨A,hA,hκ⟩:=quota_stop R.family R.makes hp
    obtain ⟨φ,hφ,hY,Z,hZ⟩:= finite_extract (𝓛:=L.lens) y (A*(q*R.family.S.a l^t)) (by filter_upwards [he,(large_mesh f l).filter_mono L.certified] with i hi hh using (hκ i.1 i.2 _ hh).trans (mul_le_mul_of_nonneg_left hi.1.measure hA))
    exact ⟨y,Z,φ,hY,hφ,hZ,he.filter_mono hφ⟩
include J W Z fx g
lemma buysTemple (hY:Height R.family.S home T Y α)(hh:α<1) {f₀:ℕ} {u:ℝ→(j:Fin n)→R.family.label (d j)}(h:Lookup R m) (ho:Moored R.family L.level)(ha:∀ᶠ r in home,∀ i:Fin n,Paid L r (u r) i≤ H (Q r)^f₀) : ∃ X:ℝ→ℕ, Height R.family.S home T X α ∧ ∃ q v:ℝ→ℝ,ValueStamp home T q ∧ RateLE home T v (-((t+1/16:ℝ)*(1-α)))∧ ∀ b:ℝ→ Fin n → Cover,∀ x:Points n,x∈conf n → Tendsto (fun r=>tag (role R.family r) (b r)) home (𝓝 x)→∀ᶠ r in home,∃ (y:ℕ×ℕ→R.family.label t) (X₀:R.family.label t) (p:Filter (ℕ×ℕ)), p.NeBot ∧ p≤L.lens∧ Tendsto y p (𝓝 X₀)∧ ∀ᶠ j in p, readingPrice R d L r (Y r) (m r) (q r) (v r) t (b r) (u r) j (y j)∧ Paintbrush R L d t r (X r) (m r) (q r) (b r) (u r) j (y j):=by
    obtain ⟨X,hX,q,v,hq,hV,hκ⟩:= assuresTemple R Z fx W J d t f₀ Y m g ho h hY hh
    refine ⟨X,hX,q,v,hq,hV,fun b x hx hv=>?_⟩; filter_upwards [hκ x b hx hv,h.spine.grows.eventually_ge_atTop (R.family.ref t),ha] with r he hr ha using scenesT R d t b (Y r) (m r) (X r) hr (u r) (q r) (v r) (he.mono fun i hi=> hi (u r) ha)
omit J W
variable (x:ℝ→ℕ)(q δ₀ :ℝ→ℝ)
include fx Z g
-- tariff δ₀ typically g^w. preserves additionally (a_m/a_l)^d. ratio remains on C.S not through C.path rep. frame comparison STILL needed.
lemma wakes (h:Lookup R m) (hp: Height R.family.S home OPE.run x α) (hh:α<1) (hq:ValueStamp home T q)(hd:ValueStamp home T δ₀): ∃ l:ℝ→ℕ, Height R.family.S home OPE.run l 1 ∧ ValueStamp home T (fun i=>a (l i)/i) ∧
      ∀ᶠ r in home,x r ≤ l r∧ l r < m r ∧ ∀ (N p:ℕ)(z:R.family.label t)(b:Fin n→ Site (R.family.side (wheel R.family r) p))(v:(i:Fin n)→R.family.label (d i)), ∀ h:Temple R d t r N p b v (q r / 2) (x r) (m r) z,
      ∀ hl:l r ≤ N,
      let P:= fun U=>liftVac R.family.path N p N U*(∏ j:Fin n,R.family.O N p (v j) (attachV R (wheel R.family r) (p:=p) b N j) U);
      ∀ U,flags (R.family.path.rep N p (l r)).p.threshold U=∅ →
         ‖GridApprox.pushTo R.family.path N p hl P U / liftVac R.family.path N p (l r) U - Spindle.awakeFull R.family (l r) N p z U‖ ≤ δ₀ r*(a (m r)/a (l r))^t:=by
   let y i:=1+H (m i); have hZ:= ((ValueStamp.const ageLarge one_pos).add ageLarge (betaStamp ageLarge h.spine)).mul (hq.div (ValueStamp.const ageLarge zero_lt_two))
   obtain ⟨l,hL,hV,h'⟩:= atop R Z fx m g hZ hd h
   have he: Monotone H:= fun i j hij=> add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono _).monotone hij) (show 0 ≤ G.slopeConstant from (Gauge.slopeConstant_pos Z.simple).le)) _
   refine ⟨l,hL,hV,?_⟩
   filter_upwards [hp.earlier hh ageLarge hL,h', hq.profit, hL.grows.eventually_ge_atTop (R.family.ref t)] with r hr ht hy hμ; refine ⟨hr.le,ht.1,fun N p z b v hz hl U hu=>?_⟩
   let H':=a (l r); let A:= a (m r); have hA:0<A:=R.family.S.a_pos _; have hB:0<H':=R.family.S.a_pos _
   obtain ⟨M,hM⟩:=hz.prime; obtain ⟨⟨R',_,hp,hqᵤ⟩,hs⟩:=hM (l r) hr.le ht.1.le; let v':= Bid.gainChart R.family.path (m r) (l r)
   let κ:= (R.family.path.levels.params (l r)).columns; have hκ:κ ≤ H (m r):=(g.money.present _).trans (he ht.1.le)
   refine (spiresUp R.family N p (l r) t R.makes _ U z _ hμ hl hs hu hp hqᵤ).trans ?_
   change (1+κ)* (q r/2*A^t/v') / H'^t ≤ _; rw [div_pow]; apply le_trans (b:=(y r*(q r/2)/v')*(A^t/H'^t))
   · apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (add_le_add_right hκ _) (show 0 ≤ q r/2*A^t/v' from div_nonneg (mul_nonneg (div_nonneg hy.le (by norm_num)) (pow_nonneg hA.le _)) (Real.exp_pos _|>.le))) (pow_nonneg hB.le _)).trans_eq; unfold y; ring
   exact mul_le_mul_of_nonneg_right ht.2.le (div_nonneg (pow_pos hA t).le (pow_pos hB t).le)
end YM.RG17
