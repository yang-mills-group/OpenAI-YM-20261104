import YM.Integration.WilsonOffsetMarkComparison
import YM.Integration.WilsonOffsetOrderPayment

/-! The entire finite colored primary comparison, with fixed extra grade,
for the genuine observed field at either actual position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetFittedPrimary
open Function MeasureTheory Filter Finset Lattice RG Wilson Labels Source MSbar.Bulk
open PhysicalNext.Repeat.Legato RGComparison.Core16.Spool
open WilsonOffsetConditionalCharge WilsonOffsetSourceBasis WilsonOffsetMarkComparison WilsonOffsetOrderPayment
open scoped Classical BigOperators
variable {G:Gauge}

def lamp (R:Run G) (d:ℕ) {n:Side} (i:(R.family.labels.level d).Index) (y:Site n) :=
  (R.family.localSection d).places (Pi.single i 1) y

def due (R:Run G) (N p m d k:ℕ) (y:Site (R.family.side (m+1) p)) (V:Config G (R.family.side m p))
    (W:(R.family.labels.level d).Index → Bool → ℝ) : Prop :=
  let S:=R.family.path.levels.clock.op m p
  let P:=R.family.path.rep N p (m+1)
  let g:=Next.SectorChange.coupling P.beta
  ∀ i b, |expect S P V (fun U=>look b (lamp R d i y U))-W i b| ≤ g^(k+order (R.family.labels.level d)+1)

def quote (R:Run G) (d m:ℕ) (v:R.family.label d) (W Z:(R.family.labels.level d).Index → Bool → ℝ) : ℂ :=
  let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (m+1))⁻¹ v
  ((R.family.S.block m).val:ℂ)^d* ∑i,x i*(paint (W i)-paint (Z i))

theorem paid (R:Run G) (hG:G.Simple) (d:ℕ) :
    ∀ᶠ m:ℕ in atTop, ∀ N p, m<N → ∀ (v:R.family.label d) (k:ℕ)
      (y e:Site (R.family.side (m+1) p)) (V:Config G (R.family.side m p))
      (W Z:(R.family.labels.level d).Index → Bool → ℝ),
      due R N p m d k y V W → due R N p m d k e V Z →
      let P:=R.family.path.rep N p (m+1)
      let g:=Next.SectorChange.coupling P.beta
      let S:=R.family.path.levels.clock.op m p
      let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (m+1))⁻¹ v
      ‖((R.family.S.block m).val:ℂ)^d*conditional S P V (fun U=>
        (R.family.localSection d).places x y U-(R.family.localSection d).places x e U)-quote R d m v W Z‖
        ≤ (∑i,‖v i‖)*g^k :=by
  filter_upwards [WilsonOffsetOrderPayment.paid R hG d] with m nums N p hm v k y e V W Z wy we
  let P:=R.family.path.rep N p (m+1)
  let S:=R.family.path.levels.clock.op m p
  let B:=((R.family.S.block m).val:ℝ)^d
  let x:=(R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (m+1))⁻¹ v
  let A:=fun i=>lamp R d i y;let D:=fun i=>lamp R d i e
  have ca (i):Continuous (A i):=(R.family.localSection d).continuous_places _ _
  have cd (i):Continuous (D i):=(R.family.localSection d).continuous_places _ _
  have hp:=P.envelope (R.makes.wilson.represents N p (m+1) hm).good
  have hk:=R.family.path.levels.transition_mass m p P.beta
  have paid:=pair hk hp V x A D ca cd W Z _ wy we
  have eq (o:Site (R.family.side (m+1) p)) :
      (R.family.localSection d).places x o =fun U=>∑i,x i*lamp R d i o U :=
    funext (fun U=>WilsonOffsetSourceBasis.expand _ _ _ U)
  change ‖((R.family.S.block m).val:ℂ)^d*conditional S P V (fun U=>
    (R.family.localSection d).places x y U-(R.family.localSection d).places x e U)-quote R d m v W Z‖ ≤ _
  rw [WilsonOffsetMarkComparison.subtract hk hp V ((R.family.localSection d).places x y)
    ((R.family.localSection d).places x e) ((R.family.localSection d).continuous_places x y)
    ((R.family.localSection d).continuous_places x e),eq y,eq e]
  unfold quote
  rw [←mul_sub,norm_mul]
  simp only [norm_pow,Complex.norm_natCast]
  apply (mul_le_mul_of_nonneg_left paid (by positivity)).trans
  let q:=(Next.SectorChange.coupling P.beta)^(k+order (R.family.labels.level d)+1)
  have eqorder:B*((∑i,‖x i‖)*(4*q))=4*B*(∑i,‖x i‖)*q:=by ring
  exact eqorder.le.trans (nums N p hm v k)

end YM.Integration.WilsonOffsetFittedPrimary
