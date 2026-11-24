import YM.PhysMS.Frame.Apply
import YM.OPE.Nesting.Endpoint
/-! Take all nonroot costs, including epsilon slack, outside estimates indexed by
    logarithmic measurement-radius costs. Used in moving-frame price transfer,
    without any lower bound on an internal scale ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysMS.Frame.Toll
open Function Set Filter Spec OPE OPE.Orbits OPE.Nesting OPE.Nesting.Tree Trace.Pilot
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
variable {n:ℕ}{T:Fin n→Nesting.Tree}
local notation "Ω" => Nesting.Tree.fork n T
set_option quotPrecheck false
local notation "D" d=> (Climb.Bel C.book).Field d

private lemma monotonicity (V:Nesting.Tree)(u w:V.Leaf→ℝ) (h:u≤w) : V.headSum u ≤ V.headSum w := by
   induction V with
   | bud=> intro i; cases i
   | fork n f ih=> rintro (x|⟨i,v⟩); exact Finset.sum_le_sum (fun j _=> h j); exact ih i _ _ (fun j=> h ⟨i,j⟩) v
private lemma fits (V:Nesting.Tree){s:V.Inner→ℝ}{r b:ℝ}(hr:0<r)(h:b ≤ r) (H: V.Tapered b 1 s) : ∀ i, V.ratios r s i ≤ 1:= by
    induction V generalizing r b with
    | bud => intro i; cases i
    | fork n f ih=> rintro (x|⟨i,v⟩); cases x; exact (div_le_one hr).mpr (H.2.1.trans h); exact ih i (s:=childAge i s) (r:=s (.inl ())) H.1 (mul_one _|>.le) (H.2.2 i) v

def interiorBill (e: (fork n T).Leaf→ℕ) (ε : ℝ) (s:(fork n T).Inner→ℝ):=
    ∏ i:Σ i,T i|>.Inner, ((fork n T).ratios 1 s (.inr i))^(-(fork n T).headSum (fun z=>(e z:ℝ)) (.inr i)-ε)
lemma paid_int (u:(fork n T).Leaf→ℕ) (ε:ℝ) (s:(fork n T).Inner→ℝ) {r:ℝ} (h:(fork n T).Tapered r 1 s): 0< interiorBill u ε s :=
    Finset.prod_pos fun _ _=>Real.rpow_pos_of_pos (h.pricePositive _ one_pos _) _
lemma lowers (u w:(fork n T).Leaf→ℕ) (h:u≤w){ε δ:ℝ}(he:δ≤ε){r:ℝ}(hb:r≤1) (s:(fork n T).Inner→ℝ) (hp:(fork n T).Tapered r 1 s): interiorBill u δ s ≤ interiorBill w ε s:= by
    refine Finset.prod_le_prod (fun i _=> (Real.rpow_pos_of_pos (hp.pricePositive _ one_pos _) _).le) (fun i _=> Real.rpow_le_rpow_of_exponent_ge (hp.pricePositive _ one_pos _) (fits (fork n T) one_pos hb hp (.inr i)) (sub_le_sub ((neg_le_neg (monotonicity (fork n T) _ _ ?_ (.inr i)))) he))
    exact fun i=> Nat.cast_le.mpr (h i)
lemma unfold_toll {d:(fork n T).Leaf→ℕ}(u:Labels S d)(ε m : ℝ)(s:(fork n T).Inner→ℝ){r:ℝ} (he:s (.inl ())=r) :
    toll (wages (Orbits.tags u)) ε m s= r^(m-weight d-ε)* interiorBill d ε s:= by unfold toll; rw [he]; rfl

section
-- For transmitting any multilinear price. Transform input marks from measurement at r.
variable {W U : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (J:ℝ→tower S) (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (H:Leading F J)
variable (P:U→∀ d:(fork n T).Leaf→ℕ, MultilinearMap ℂ (fun i=>S.Field (d i)) W) {s:U→(fork n T).Inner→ℝ}
    {l:Filter U} {r:U→ℝ} (hr:Tendsto r l trail) (ht:∀ᶠ i in l, (fork n T).Tapered (r i) 1 (s i)) (hs:∀ᶠ i in l,s i (Sum.inl ())= r i)
    {m ε:ℝ} (he:0<ε) {d:(fork n T).Leaf→ℕ}
include R hr ht hs H he
lemma rate_now (hv:(j:(fork n T).Leaf)→D (d j))
    (h:∀ e:(fork n T).Leaf→ℕ,e ≤ d → ∀ (u:Labels S e) (ε:ℝ),0<ε → ∀ᶠ i in l, ‖P i e u‖ ≤ toll (wages (Orbits.tags u)) ε m (s i))
    (hp:∀ e,∀ he:e≤d,∀ᶠ i in l,∀ x:Labels S e, P i e x= P i d (fun j=> F.sector.derivatives.rise (he j) (x j))) :
    RateLE l (LogV ∘ r) (fun i=> ((↑((interiorBill d ε (s i))⁻¹):ℂ) • P i d (fun j=> J (r i) (d j) (hv j)))) (-m) := by
     let A(i:U)(e:(fork n T).Leaf→ℕ):= (↑((interiorBill d ε (s i))⁻¹):ℂ) • P i e
     refine total F R J H hr hv (-m) A (fun e he' => (hp e he').mono fun i hi v=> congr_arg _ (hi v)) ?_
     intro e he' v; apply RateLE.mono (b:=weight e+(-m)) (a:=-(m-weight e)) _ (by linarith only [])
     refine pays_power (r:=r) ?_ hr; intro δ hδ
     let q:= min δ ε; have hq : 0 < q:= lt_min hδ he
     have hOne : ∀ᶠ i in trail, i ≤ 1:= (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)).filter_mono (@nhdsWithin_le_nhds ℝ _ (0:ℝ) _)
     filter_upwards [h e he' v _ hq,ht,hs,hr.eventually hOne,hr.eventually (self_mem_nhdsWithin)] with i hi hL hv hT hx; rw [unfold_toll v _ _ (s i) hv] at hi
     let b:=interiorBill d ε (s i); have hB:0<b:= paid_int d ε (s i) hL; change ‖(↑(b⁻¹):ℂ) • P i e v‖ ≤ _
     rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (by positivity : 0≤b⁻¹)]; apply (inv_mul_le_iff₀ hB).mpr
     rw [mul_comm b]; exact hi.trans (mul_le_mul (Real.rpow_le_rpow_of_exponent_ge hx hT (sub_le_sub_left (min_le_left ..) _)) (lowers e d he' (min_le_right ..) hT (s i) hL) ((paid_int e q (s i) hL).le) (Real.rpow_nonneg (le_of_lt (show 0<r i from hx)) _))
end
end YM.PhysMS.Frame.Toll
