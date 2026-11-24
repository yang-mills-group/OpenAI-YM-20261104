import YM.QuadraticLocal.Earn.Cable
import YM.Integration.WilsonThermometerRegisteredPairRoom
import YM.Integration.WilsonThermometerAlignedCells

/-! The two independent microscopic displacements of the submitted compact three-point
profile fit the same original coarse capture halo, uniformly before either regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCapturedPaths
open Lattice Wilson RG Extraction Cells RG12 Filter MeasureTheory Set XSpace Finset Source Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity FVA1 ActualRunUnmaskedPartners
open PhysicalNext.Repeat.Legato
open WilsonThermometerAlignedCells
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)

theorem original (φ:Test 3) : ∃K:ℕ, ∀j:ℕ,
  ∀ (N per:ℕ) (live:j ≤ N) (r:ℝ), |r|≤R.family.S.a j → ∀y:Site (R.family.side N per) × Site (R.family.side N per),
  mass (R:=R) r (N,per) φ y≠0 → ∀v:Fin 3,
  let x:=(R.family.S.toDepth live per).parent (atOrigin y v)
  stop (0:Site (R.family.side j per)) (Earn.Cable.link 0 x)=x ∧ (Earn.Cable.link 0 x).length≤4*K:=by
  obtain ⟨K,shape⟩:=WilsonCapturedPrimaryCaptureRoom.shape φ
  refine ⟨2*(K+1)+1, ?_⟩
  intro j N per live r radius y tested
  obtain ⟨c,x,hx,location⟩:=supported (R:=R) r (N,per) φ tested
  let S:=R.family.S
  let g:=S.toDepth live per
  let z:=address (S.a N) (r • x)
  have fine:=S.a_pos N
  have coarse:=S.a_pos j
  have expand:S.a N*(g.count.val:ℝ)=S.a j:=S.embeds_scale g
  have count : (1:ℝ) ≤ (g.count.val:ℝ) := by exact_mod_cast g.count.property
  have mono:S.a N ≤ S.a j:=by rw [←expand];simpa only [mul_one] using mul_le_mul_of_nonneg_left count fine.le
  have fee (v:Fin 3) (a:Axis):|S.a N*(z v a:ℝ)|≤((K+1:ℕ):ℝ)*S.a j:=by
    have vertex:=(Extraction.tile_bounds fine ((r • x) v a) (z v a)).mp rfl
    change S.a N*((z v a:ℝ)-1)<r*x v a ∧ r*x v a≤S.a N*(z v a:ℝ) at vertex
    have mag:|S.a N*(z v a:ℝ)|≤|r*x v a|+S.a N:=by
      rw [abs_le]; exact ⟨by linarith [neg_abs_le (r*x v a),vertex.2],
        by linarith [le_abs_self (r*x v a),vertex.1]⟩
    rw [Nat.cast_succ,add_mul,one_mul]
    apply mag.trans (add_le_add _ mono)
    rw [abs_mul,mul_comm (K:ℝ)]
    exact mul_le_mul radius (shape x hx v a) (abs_nonneg _) coarse.le
  intro v
  have far:∀a, |S.a N*((z v-z 0) a:ℝ)|≤((2*(K+1):ℕ):ℝ)*S.a j:=by
    intro a
    change |S.a N*((z v a-z 0 a:ℤ):ℝ)|≤_
    rw [Int.cast_sub,mul_sub]
    calc
      _ ≤ |S.a N*(z v a:ℝ)|+|S.a N*(z 0 a:ℝ)| := abs_sub _ _
      _ ≤ ((K+1:ℕ):ℝ)*S.a j+((K+1:ℕ):ℝ)*S.a j := add_le_add (fee v a) (fee 0 a)
      _ = _ := by push_cast;ring
  have sockets (w:Fin 3): wrap (S.side N per) (z w)=atOrigin y w+c := congrFun location w
  have pos:atOrigin y v=wrap (S.side N per) (z v-z 0):=by
    rw [map_sub,sockets,sockets]
    change _=(_+c)-(0+c);abel
  change stop 0 (Earn.Cable.link 0 _) = _ ∧ (Earn.Cable.link 0 _).length ≤ _
  refine ⟨Earn.Cable.link_stop ..,?_⟩
  rw [pos]
  apply (Earn.Cable.link_height ..).trans
  rw [separation_comm]
  exact Nat.mul_le_mul_left 4 (WilsonThermometerRegisteredPairRoom.integer S live _ _ far)

end YM.Integration.WilsonThermometerRegisteredCapturedPaths
