import YM.Integration.WilsonReflectedMicroscopicSites

/-! An earlier physical filing date stays fixed while the real reporter moves.
Each reflected copy can afford the common weight at the true capture point. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReflectedTerminalWallet
open Set Function Filter Lattice Wilson RG OPE MergeProof Ribbons Accent Source Overlay Bid
open ManyCopies PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage Cells
open Push.GridApprox Trace.Physical.GermGraph
open scoped BigOperators Topology Matrix.Norms.Frobenius Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple)
variable (book:OPE.Package R.family R.w (mutt R.alloy.B.a R.Q) R.doors)
variable {A:Type*} {l:Filter A} {T Z E:A → ℝ} {b:A→ℕ}
local notation "C" => R.family
local notation "L" => R.family.path.levels
local notation "δ" => renal R.alloy.B.a
local notation "φ" => near R.alloy.B.a
local notation "X" => bling R.alloy.B.a

omit simple book in
theorem constant {V : Type*} (w:ℝ) (s:ℕ→ℝ) (u b:ℕ) (v:V) :
    march (fun _:V=>w) s u b v=march (fun _:Unit=>w) s u b () :=by
  induction b with
  | zero=>rfl
  | succ b ih=>simp only [march];split <;> simp [ih]

include simple book in
theorem original (u d:ℕ) (live:R.family.ref d ≤ u) (time:Tendsto T l atTop)
    (cap:Height R.family.S l T b 1) (issued:RateIs l T Z 0) (capital:RateIs l T E (-(d:ℝ))) :
    ∀ᶠ i in l,
      let w:=Real.exp (((d:ℝ)+1/16)*T i)
      march (fun _:Unit=>w) φ u (b i) () ≤ δ (b i)*(Z i/(16*X (b i))) ∧
      32*(1+(R.family.path.levels.params (b i)).columns)*w*‖alto R.family.path u d‖*
        (E i/gainChart R.family.path (b i) u) ≤ fly R.alloy.B.a d u/2 :=by
  let w:=fun i=>Real.exp (((d:ℝ)+1/16)*T i)
  have hw:RateIs l T w ((d:ℝ)+1/16):=RateIs.exp _ time
  have gain:RateIs l T (fun i=>gainChart R.family.path (b i) u) (1/8:ℝ):=by
    apply RateIs.exp'
    have base:=(tendsto_const_nhds (x:=R.family.S.scale u)).div_atTop time
    simpa only [sub_zero,mul_one,←sub_div,←mul_div_assoc] using! ((cap.pace.sub base).const_mul (1/8:ℝ))
  have hu:=RateIs.const time (book.system.grows d u live)
  have hq:=(height0 (mintN R.family simple|>.1) cap).mul
    (issued.div ((RateIs.const (c:=16) time (by norm_num)).mul (height0 (banket R.family simple) cap)))
  have low:=(hw.mul ((cap.mesh.div (RateIs.const time (R.family.S.a_pos u))).power (d+1))).mul
    ((flyRate simple cap d).div hu)
  have a:0 < ‖alto R.family.path u d‖:=by rw [alto_norm];exact inv_pos.mpr (pow_pos (R.family.S.a_pos _) _)
  have col:=(RateIs.const (c:=32) time (by norm_num)).mul ((RateIs.const (c:=1) time one_pos).add (height0 (fuNote R.family) cap) time)
  have upper:=((col.mul hw).mul (RateIs.const time a)).mul (capital.div gain)
  filter_upwards [hq.overtakes (low.pays time) time (by push_cast;linarith),
    (hu.div (RateIs.const time zero_lt_two)).overtakes (upper.pays time) time (by rw [max_self];linarith),
    cap.grows.eventually_ge_atTop u] with i below paid ordered
  exact ⟨(seeing R.family d book.system (Real.exp_pos _) (b i) u live ordered).trans below.le,paid.le⟩
end YM.Integration.WilsonReflectedTerminalWallet
