import YM.OPE.Gallery.Intake
/-! # Finite overhead bookkeeping -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float Labels Bid Cadet Drapery
open scoped Topology BigOperators Classical
variable {G:Gauge}{I J V L B X : Type}[Fintype V][DecidableEq V]
variable [Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype L][DecidableEq L][Fintype B][DecidableEq B][Fintype X][DecidableEq X]
variable {H:History G}{N p k m i j b T ℓ μ:ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
    {δ φ ψ η:ℕ→ℝ}{z r:ℕ→ℕ}{P:Playout H p b N V}{A:Fibers I J}
variable {α:ℝ}{w:ℕ→I→ℝ}{d c e:ℕ} (s:Finset J)
set_option quotPrecheck false
local notation "χ"=> (H.S.block i).val
-- Awake ledger primitive per-token and aggregation
set_option quotPrecheck false
def cell (H:History G)(i j c:ℕ)(α w:ℝ):= (H.S.a j/H.S.a i)^4*α^c*w
def bill (H:History G)(i j c:ℕ)(α:ℝ)(w:I→ℝ)(A:Fibers I J)(u:J) := ∏ k∈A.contents u, cell H i j c α (w k)

variable {c':ℕ}
variable (K:Fibers I L)(C:Fibers L J) {u:I}{v:J}{l:L}
lemma cell_pos {w:ℝ}(ha:0<α)(hb:0<w):0<cell H i j c α w:= mul_pos (mul_pos (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _) (pow_pos ha _)) hb
lemma bill_pos (v:L){w:I→ℝ}(ha:0<α)(hb:∀ i,0<w i): 0 < bill H i j c α w K v:=prod_pos fun i _=> cell_pos ha (hb i)
lemma cellMore {w w':ℝ} (hp:i ≤ k)(he:c' ≤ c)(ha:0 ≤ α)(hb:α≤1)(hw:0≤ w)(hx:w≤ w'): cell H i j c α w ≤ cell H k j c' α w':=by
    unfold cell; refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (div_nonneg (H.S.a_pos j|>.le) (H.S.a_pos i|>.le)) (div_le_div_of_nonneg_left (H.S.a_pos _|>.le) (H.S.a_pos _) ((H.S.strictAnti).antitone hp)) _) (pow_le_pow_of_le_one ha hb he) (pow_nonneg ha _) (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _|>.le)) hx hw (mul_nonneg (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _|>.le) (pow_nonneg ha _)) -- lemma?
lemma cell_tariff (x:ℝ): cell H (i+1) j c α x= cell H i j c α x * (χ:ℝ)^4:=by rw [cell,Schedule.a_step]; unfold cell; ring_nf; rw [inv_inv]; ring
lemma cellAdv {c' :ℕ}{w:ℝ}: cell H i j (c+c') α w= α^c'*cell H i j c α w:=by unfold cell; rw [pow_add];ring
private lemma credit {s:Finset I}{V W:I→ℝ}{a:ℝ}(ha:0 ≤ a)(hs:s.Nonempty)(h:a ≤ 1)(hv:∀ i∈s,V i≤a*W i)(he:∀ i,0<V i)(hw:∀ i,0<W i) : ∏ i∈s,V i ≤ a * ∏ i∈s,W i:= calc
   _ ≤ ∏ i∈s,(a*W i) := Finset.prod_le_prod (fun i _=>(he i).le) hv
   _ = a^s.card * ∏ i∈s,W i :=by rw [Finset.prod_mul_distrib,Finset.prod_const] -- specify
   _ ≤ _ := mul_le_mul_of_nonneg_right (show a^s.card ≤ a from (by simpa only [pow_one] using pow_le_pow_of_le_one ha h (show 1≤ s.card from card_pos.mpr hs))) ((prod_pos fun i _=> hw i).le)
variable (q : I→ℝ)(x y : ℝ)
local notation "Γ" => H.S.scale
local notation "Ω" => H.S.a
local notation "Σ0"=> ((H.S.block i).val:ℝ)
variable (B0:BudgetStop H D δ ψ φ z η r μ) {u0:I→ℝ}
lemma pay_single (hp:A.Solo v) : bill H i j c α q A v= cell H i j c α (q (A.twig v)):= by rw [bill,hp.content,prod_singleton]
lemma paidOne (hr:∀ i∈s,A.Solo i)(hp:splitAt A K C)(hh:C.bunch l ∈ s)(hw:0<α)(he:α≤1)(hx:0 ≤ w i (K.twig l))(ht:i≤j): bill H i j c α (w i) K l ≤ w i (K.twig l):=by
    rw [pay_single (w i) (hp.dorm1 l (hr _ hh))]; unfold cell; refine mul_le_of_le_one_left hx (mul_le_one₀ ?_ (pow_nonneg hw.le _) (pow_le_one₀ hw.le he)); apply pow_le_one₀ (by have ha:=H.S.a_pos i; have hb:=H.S.a_pos j; positivity) ((div_le_one (H.S.a_pos i)).2 ((H.S.strictAnti).antitone ht))
lemma awaken (hp:splitAt A K C)(hu:C.bunch l ∉ s)(hc:∀ k:I,A.bunch k∉s → w i k=w (i+1) k)(hf:∀ k,0<w i k)(ht:∀ k,0<w (i+1) k)(h:0<α) : bill H i j c α (w i) K l ≤ bill H (i+1) j c α (w (i+1)) K l / Σ0^4:=by
    have h0:1 ≤ Σ0:=le_trans one_le_two (size_enough ..); have hQ:1 ≤ Σ0^4:= one_le_pow₀ h0; have hV:0 < Σ0^4:=zero_lt_one.trans_le hQ; rw [div_eq_inv_mul]; unfold bill; refine credit (inv_pos.mpr hV|>.le) (widths ..) (inv_le_one_of_one_le₀ hQ) ?_ (fun k=>cell_pos h (hf k)) (fun k=>cell_pos h (ht k))
    intro k hk; rw [hc k (fun hh=> hu (((show A.bunch k=C.bunch l from (hp k).trans (congr_arg C.bunch ((K.focuses ..).1 hk)))) ▸ hh)), cell_tariff]; rw [mul_comm _ (_*_),mul_assoc,mul_inv_cancel₀ hV.ne',mul_one]
lemma stepping {z:ℝ}(hη:0<z)(h:0<α)(hw:∀ i, z*u0 i ≤ q i)(ht:∀ i,0<u0 i)(u:I) : z*cell H i j c α (u0 u) ≤ cell H (i+1) j c α (q u):=by
    have hp : z*cell H i j c α (u0 u) ≤ cell H i j c α (q u):=by unfold cell; rw [mul_left_comm]; apply mul_le_mul_of_nonneg_left (hw u); exact mul_nonneg (pow_pos (div_pos (H.S.a_pos _) (H.S.a_pos _)) _|>.le) (pow_pos h _|>.le)
    apply hp.trans; rw [cell_tariff]; exact le_mul_of_one_le_right (cell_pos h ((mul_pos hη (ht u)).trans_le (hw u))|>.le) (one_le_pow₀ (one_le_two.trans (size_enough ..)))
lemma consumingCost {K:Fibers I L} {C:Fibers L J} (hr:∀ i∈s,A.Solo i)(hp:splitAt A K C)(h1:0<η i)(h2:η i ≤ 1)(hh:0<α)(hc:∀ k:I,A.bunch k∉s → w i k=w (i+1) k)(hf:∀ k,0<w i k)(ht:∀ k,0<w (i+1) k)(hS:∀ k,η i*w i k ≤ w (i+1) k)(l:L): η i* bill H i j c α (w i) K l ≤ bill H (i+1) j c α (w (i+1)) K l :=by
    by_cases ha:C.bunch l∈s
    · rw [pay_single _ (hp.dorm1 l (hr _ ha)),pay_single _ (hp.dorm1 l (hr _ ha))]; exact stepping _ h1 hh hS hf _
    exact (mul_le_of_le_one_left (bill_pos K _ hh hf|>.le) h2).trans ((awaken s K C hp ha hc hf ht hh).trans (div_le_self (bill_pos _ _ hh ht|>.le) (one_le_pow₀ (one_le_two.trans (size_enough ..)))))
-- combine budgets. 8 token haircut per changed name, pay scan cost on each fragment.v
variable {V₀ V₁ : I→ℝ}{Z α' :ℝ}
lemma combine_budget (hp:splitAt A K C)(hS:∀ k,η i*V₀ k ≤ V₁ k)(ht:∀ i,0<V₀ i)(he:∀ i,0<V₁ i)(h1:0<η i)(h2:η i≤ 1)(hf:0<α)(hh:α≤1)(hX:8*α ≤ η i * license H δ T ℓ i)(hm:license H δ T ℓ i ≤ 1) (hw:0<license H δ T ℓ i)(hg:c<d) (k:J) : bill H i j d α V₀ A k ≤ grouped H δ T ℓ i (bill H (i+1) j c α V₁ K) C k/8:=by
    let S:=license H δ T ℓ i; have ht' : 0<S/8:= div_pos hw (by norm_num); have hh': S/8≤1:=by unfold S; linarith only [hm]
    let K'(k):= bill H (i+1) j c α V₁ K k; let g:=cell H i j d α ∘ V₀; let v:= C.contents k
    have hz(x:L): ∏ i∈ K.contents x,g i ≤ (S/8)*K' x:=by
       refine credit ht'.le (widths ..) hh' ?_ (fun i=> cell_pos hf (ht i)) (fun i=> cell_pos hf (he i)); intro k hk; let q0:= cell H (i+1) j c α (V₀ k); let q1:= cell H (i+1) j c α (V₁ k)
       have hq: g k ≤ α * cell H i j c α (V₀ k) := (cellMore (i:=i) (k:=i) (j:=j) (c:=d) (α:=α) le_rfl hg hf.le hh (ht k|>.le) le_rfl).trans_eq ((cellAdv (H:=H) (i:=i) (j:=j) (c:=c) (c':=1) (α:=α) (w:=V₀ k)).trans (by rw [pow_one]))
       have he_:η i= η i:=rfl
       apply hq.trans; have hX' : α ≤ (S/8)*η i := by linarith only [hX] -- commute ring
       exact (mul_le_mul_of_nonneg_right hX' (cell_pos hf (ht k)|>.le)).trans ((mul_assoc ..|>.le).trans (mul_le_mul_of_nonneg_left (stepping V₁ h1 hf hS ht k) ht'.le))
    unfold bill; rw [hp.group_prod]; unfold grouped; rw [div_eq_inv_mul]; apply credit (by norm_num) (widths ..) (by norm_num) ?_ (fun a=> prod_pos fun k _=> cell_pos hf (ht k)) (fun a=> mul_pos hw (bill_pos K a hf he))
    intro i hi; exact (hz i).trans_eq (by dsimp only [g,S,K',comp_apply]; ring)
end YM.MergeProof.Ribbons.ManyCopies.Cadet.Lecture
