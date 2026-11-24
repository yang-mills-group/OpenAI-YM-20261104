import YM.Integration.WilsonMarkedIndependentWindingCourse
import YM.WilsonCoeffUV.Reclosure.Paths.RetainBase

/-! The actual bare Wilson vacuum enters the winding induction at any prescribed width. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentBareWinding
open Function Filter Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

private theorem row (G:Gauge)(e l:ℕ){s:ℝ}(hs:0<s):
    ∃B:ℝ,0≤B ∧ ∀n:Side,Sight (sprig (eWilson (G:=G) (c:=n)) 2 e (l+1)) (moon G e (l+1)) s B:=by
  let t:ℝ:=l+1
  have ht:0<t:=by dsimp [t];positivity
  let w:=4*t*s
  have hw:0<w:=by dsimp [w];positivity
  obtain ⟨A,hA⟩:=moon_bill G e (l+1) w hw.le
  have scale:s≤perchA w l:=by
    apply le_min
    · dsimp [w,t];nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) l) hs.le]
    · change s≤(w/(2*(↑(l+1):ℝ)))/2
      rw [le_div_iff₀ (by norm_num),le_div_iff₀ (by positivity)]
      dsimp [t,w];push_cast;ring_nf
      exact le_rfl
  have paid(n:Side):Sight (lagoon (moon G e (l+1)) n) (moon G e (l+1)) s (A*(hinges w l+1)):=
    (bridgeA hA hw (moon_pages G e (l+1)).road).mono scale
  exact ⟨_,(paid 1).bound.1,fun n=>moon_wrap G e l n ▸ paid n⟩

theorem original (R:Run G)(e:ℕ){s:ℝ}(hs:0<s):
    ∃B:ℝ,1≤B ∧ ∀N,WilsonFiniteVacuumWindingDate.positive R.family.path.levels R.metals.O e N N s B:=by
  choose C hC receipt using fun q:Fin (e+1) × Fin (e+2)=>row G q.1.val q.2.val hs
  let B:=1+∑q,C q
  have nn:0≤∑q,C q:=Finset.sum_nonneg fun q _=>hC q
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro N n a _ ha l hl
  let q:Fin (e+1) × Fin (e+2):=(⟨a,by omega⟩,⟨l,by omega⟩)
  have small:C q≤∑t,C t:=Finset.single_le_sum (fun t _=>hC t) (Finset.mem_univ q)
  have hit:Sight (sprig (eWilson (G:=G) (c:=n)) 2 a (l+1)) (moon G a (l+1)) s B:=
    (receipt q n).more (by dsimp [B];linarith)
  change Sight ((story R.family.path.levels R.metals.O N N).1 n a (l+1))
    ((story R.family.path.levels R.metals.O N N).2 a (l+1)) s B
  rw [story_top]
  simpa only [tale,topW,lop,if_neg (Nat.succ_ne_zero l)] using hit

open WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonMarkedIndependentWinding (Folded)
open IndependentSourcePathFamily
variable {I:Type}[Fintype I][DecidableEq I]{D:I→ℕ}
variable {I₀ I₁:I→Type}[∀i,Fintype (I₀ i)][∀i,Fintype (I₁ i)]
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

/-- The complete occupied log after a real first deposit, a fresh birth, and any further finite
history. Both the finite and the independently contracted cover use their own previous inputs. -/
theorem received (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (e:ℕ)(K k:I→ℕ)(a:Loc G 1)(old:Finset I)(X:∀i,I₀ i → Seed G (D i))(Y:∀i,I₁ i → Seed G (D i))
    (hX:∀i z,(X i z).rank≤k i+(X i z).head)(hY:∀i z,(Y i z).rank≤k i+(Y i z).head){s:ℝ}(hs:0<s):
    ∀ᶠj:ℕ in atTop,∀ b:ℕ,j≤b→∃ C σ:ℝ,1≤C ∧ 0<σ ∧
    Folded R u tags (N:=b+1) (b:=b) (j:=j) (e:=e) K k
      (WilsonMarkedIndependentWindingCourse.received R K k (b+1) b old X Y) σ C:=by
  obtain ⟨B,hB,base⟩:=original R e hs
  filter_upwards [WilsonMarkedIndependentWindingCourse.deposited R u tags simple v funded e K k a old X Y
    hX hY hs] with j paid
  intro b live
  obtain ⟨d,C,σ,hC,hσ,step⟩:=paid b live
  exact ⟨C*B^d,σ,one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hB),hσ,
    step (b+1) (Nat.lt_succ_self _) B hB (base (b+1))⟩

end YM.Integration.WilsonMarkedIndependentBareWinding
end
