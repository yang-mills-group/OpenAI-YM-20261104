import YM.RG05Readout.Capture.Fronds
/-!
# Near-geometry repair rate

All shapes in height/range with measured base. Constant and transient sources
only in this same scheduling witness. Supports V labels arbitrary. Does NOT
prove any subpower losses repayable in perturbative coefficient precision.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter MeasureTheory Lattice Wilson RG MergeProof
open Address Native View Bid PhysicalNext.Repeat Legato Bandage OPE Ribbons
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {p k d :ℕ} {E:Type} {l:Filter E} {D: Address.Rail C}
    {B:ℝ} {n m:E→ℕ} {T r f:E→ℝ}
set_option quotPrecheck false
local notation "Z"=> C.path.levels
local notation "s"=> C.S.scale
local notation "β"=> C.path.levels.clock.hatBeta
local notation "α"=> C.S.a
local notation "U"=> C.path.levels.budget
local notation "δ"=> renal C.path.levels
local notation "Y"=> C.S.block
variable (hw:Storage C D)(hG:G.Simple)(ht:Tendsto T l atTop)(hm:Height C.S l T m 1)(hn:Height C.S l T n 1)
    (hh:∀ᶠ i in l,n i < m i)(hc:∀ᶠ i in l,CaptureW C (n i) (m i) (r i) B)(he:4 < B) {q:E→ℝ}
include hw hG ht hm hn hh hc he
lemma slices (hq:RateIs l T q 0)(d k:ℕ): RateIs l T (fun i=> Many.envelope C (m i) (d+1) k (q i) (n i+1)) 0:=by
    let v i:= rusty C (m i) k (n i+1)
    have hx: RateIs l T v 0:=by
        have h := sizes_rust (k:=k) hw hG ht hm hn (hh.mono (fun _=> le_of_lt)) hc he
        apply RateIs.of_sandwich h ((RateIs.const ht (c:=1) one_pos).pays ht) (hh.mono fun i hi=>?_) (Eventually.of_forall fun i=>(rust_paid _).2) ht
        rw [rust_local hi]; exact mul_le_of_le_one_right (rust_paid _).1.le (inv_le_one_of_one_le₀ (one_le_pow₀ (Z|>.fits.delayed _|>.le)))
    have hs:= Height.step (m:=n) hn (Z).fits.mesh -- syntax
    let J:ℕ→ℕ:= fun i=>i+1; let P i:= Many.total C (q i) (d+1) (m i) (J (n i))
    have hu: RateIs l T P 0:=by
       refine ((hq.mul ((hs.mesh.div hm.mesh).power (d+1))).swap (by ring)).congr ?_
       filter_upwards [hh] with i hi; unfold P J Many.total; rw [dif_neg (show ¬m i<n i+1 by omega)]
    exact (((hx.mul (((RateIs.power (n:=k) (beta_tends hG hs)).inv).div hu))).swap (by ring)) -- ratepower
omit hm hc he hh
lemma payblock : RateIs l T (fun i=> (↑((Y (n i)).val):ℝ)) 0:=by
    refine RateIs.of_sandwich (RateIs.const ht (c:=1) one_pos) (RateIs.pays (beta_tends hG hn) ht) (Eventually.of_forall fun i=>?_) ((hn.grows.eventually (shifts hw hG)).mono fun i hi=>hi.2.1) ht
    exact_mod_cast (Y (n i)).property
variable {w:Worth} {ρ:ℕ→ℕ}
include hm hh hc he
lemma scale_receipt (L: OPE.Package C w ρ D) (hq:RateIs l T q 0)(d k b:ℕ)(hp:0<b): RateIs l T (fun i=> fee C (m i) (n i) d k b (q i)) 0:=by
    have h := slices hw hG ht hm hn hh hc he hq d k
    have hY := height0 (mintN C hG|>.1) hn; let P i:=(δ (n i))* (Many.envelope C (m i) (d+1) k (q i) (n i+1))* ((↑((Y (n i)).val):ℝ)⁻¹) ^(4+d)
    have he':RateIs l T P 0:= ((hY.mul h).mul ((payblock hw hG ht hn).inv.power (4+d))).swap (by ring)
    have hQ:RateIs l T (fun i=>crust C (m i) (n i) d k (q i)) 0:=by
       let f i:= P i/(2*(1+P i)); let Q:=(RateIs.const ht (c:=1/2) (by norm_num)); have h' : RateIs l T f 0:= (he'.div ((RateIs.const ht (c:=2) two_pos).mul ((RateIs.const ht (c:=1) one_pos).add he' ht))).swap (by rw [max_self];ring)
       refine RateIs.of_sandwich h' (Q.pays ht) ?_ (Eventually.of_forall fun i=>min_le_left ..) ht
       filter_upwards [he'.pos] with i hi; refine le_min ((div_le_iff₀ (by positivity)).mpr ?_) ((div_le_iff₀ (by positivity)).mpr ?_)
       · linarith only
       change P i ≤ P i*(2*(1+P i)); nlinarith only [hi,sq_nonneg (P i)]
    have hx:RateIs l T (fun i=>syrup C (m i) (n i) d k b (q i)) 0:= (((hY.div (RateIs.const (c:=(b:ℝ)) ht (Nat.cast_pos.mpr hp))).mul hQ).div (height0 (billed C hG L.accounting) hn)).swap (by ring)
    exact (hx.power b).swap (by ring)
end YM.RG05Readout.Many
