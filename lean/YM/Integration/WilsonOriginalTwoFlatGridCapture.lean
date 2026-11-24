import YM.RG16.Unmasked.Exit
import YM.Integration.WilsonOriginalTwoFlatGrid

/-! Buy the original reflected product on arbitrary embedded separated nodes.
Only the actual capture and upper dates have to agree in spatial height.
In particular their mesh ratio may be a fixed power of the inverse coupling. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatGridCapture
open Function Set Filter MeasureTheory OPE Lattice Wilson RG Next.Rank Source Overlay Bid Push.GridApprox
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories RG16 RG16.Literal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage Trace.Physical.GermGraph
open scoped Topology Matrix.Norms.Frobenius Classical BigOperators ContDiff
variable {G:Gauge}(R:Run G)(hG:G.Simple){r D W}(L:Package R.family W r D)
variable {I:Type}[Fintype I][DecidableEq I][Nonempty I](d:I→ℕ)
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "σ" => R.family.S.scale
local notation "near₀" => near R.family.path.levels
local notation "δ" => renal R.family.path.levels
local notation "cost" => bling R.family.path.levels
local notation "rents" => fly R.family.path.levels

def word (j N p:ℕ)(top:j≤N)(o:I → Cover)(Y:∀i,(C).label (d i)):Cut C N p :=
  fun U=>∏i,(C).O N p (Y i) (((C).S.toDepth top p).embed (snap C j p o i)) U

include hG L in
theorem original {J u:ℕ}(stop:Stop C 0 J u)(s:ℕ→ℕ)(capture:Height (C).S atTop σ s 1)
    (M:ℕ→ℝ)(salary:RateIs atTop σ M 0):
    ∀ᶠ j:ℕ in atTop,∀ok:u ≤ s j,∀hj:s j+1<j,∀N p:ℕ,∀hN:j<N,
    ∀ (o:I → Cover), (∀i,8*‖(C).S.gridPoint j (o i)‖≤(C).S.a (s j+1)) →
    (Pairwise fun i i'=>2*(C).S.a j*(((P).budget j).B:ℝ)^2
      ≤ ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀Y:∀i,(C).label (d i),(∀i,Spindle.paid C (d i) j N p (Y i) ≤ M j) →
    let F:=word R d j N p hN.le o Y
    ‖(C).omega N p F-WilsonThermometerUnitFilingCoarse.reading R (N:=N)
      (credit C N p 0 F (s j) (by omega)) u ok‖≤Real.exp (-(1/32:ℝ)*σ j):=by
  let n:=Fintype.card I
  obtain ⟨y,hy,hup,hprice⟩:=halls hG L.halos n (show 0<n from Fintype.card_pos)
  let a i (j:ℕ):=rents (d i) j/M j
  let Z (j:ℕ):=ManyCopies.initial (C).path δ near₀ (s j) j (y j) (∏i,a i j) n
  have each(i:I):RateIs atTop σ (a i) 0:=
    ((flyRate hG (normal_height C) (d i)).div salary).swap (by ring)
  have hz:RateIs atTop σ Z 0:=
    (Height.gathered capture (normal_height C) (C).S.divergent (height0 hy (normal_height C))
      (RateIs.prod («S»:=Finset.univ) (fun i _=>each i) (C).S.divergent) hG n).swap (by simp)
  let E (j:ℕ):=terminalCost C 0 (s j) (Z j)
  have he:RateIs atTop σ E (-(0:ℕ):ℝ):=(key_cost capture (C).S.divergent hz hG 0).swap (by ring)
  have ahead:=capture.step (P).fits.mesh
  have tiles:=((height0 (briar C hG L.accounting) ahead |>.power 2).add
    (RateIs.const (C).S.divergent one_pos) (C).S.divergent).mul ahead.mesh
  obtain ⟨z,cuts⟩:=L.productCuts.mother
  obtain ⟨late,field⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatGrid.chamber C d R.makes J)
  have price:∀ᶠ j:ℕ in atTop,2*(stakes C J u/weight C 0 j) + E j/gainChart (C).path (s j) u
      ≤Real.exp (-(1/32:ℝ)*σ j):=by
    have a₀:=RateIs.const (c:=stakes C J u) (C).S.divergent (show 0<stakes C J u from Real.exp_pos _)
    have bw (e:ℕ):RateIs atTop σ (RG16.Literal.weight C e) (e+1/16:ℝ):=RateIs.exp _ (C).S.divergent
    have b₀:=bw 0
    have a₁:=((RateIs.const (C).S.divergent zero_lt_two).mul (a₀.div b₀)).pays (C).S.divergent
    have a₂:=(he.div (gain_toward C u capture)).pays (C).S.divergent
    exact ((RateIs.exp (-(1/32:ℝ)) (C).S.divergent).overtakes (a₁.addMax a₂ (C).S.divergent)
      (C).S.divergent (by norm_num)).mono fun _ h=>h.le
  filter_upwards [eventually_ge_atTop late,salary.pos,price, hz.pos,
    capture.grows.eventually (plenty P J (lensScope C 0)),
    (RateIs.const (C).S.divergent ((C).S.a_pos J)).overtakes (tiles.pays (C).S.divergent)
      (C).S.divergent (by simp),
    eventually_all.mpr (fun i:I=>eventually_ge_atTop ((C).ref (d i))),
    late_march C hG L u 0 (stop.doors 0).post capture he hz] with j hf source good hzj old room ref board
  intro us sj N p hN o hous apart Y charge F
  obtain ⟨_,zero,spaced⟩:=WilsonOriginalTwoFlatGrid.locations C sj.le o hous apart p
  have pos(i:I):0<a i j:=div_pos (L.system.grows (d i) j (ref i)) source
  have money(i:I):a i j*Spindle.paid C (d i) j N p (Y i)≤rents (d i) j:=
    (mul_le_mul_of_nonneg_left (charge i) (pos i).le).trans_eq (div_mul_cancel₀ _ source.ne')
  have sm:J ≤ s j+1:=stop.live.1.trans (us.trans (s j).le_succ)
  let g:=(C).S.toDepth sm p
  have fit:(((P).budget (s j+1)).B^2+1:ℕ) ≤ g.count.val:=by
    have m:((((P).budget (s j+1)).B:ℝ)^2+1) ≤ g.count.val:=
      le_of_mul_le_mul_right (room.le.trans_eq (((C).S.embeds_scale g).symm.trans (mul_comm ..))) ((C).S.a_pos _)
    exact_mod_cast m
  obtain ⟨ins,unit⟩:=field N (hf.trans hN.le) p (s j) j hN.le sm sj.le o hous
  have main:=WilsonOriginalTwoFlatCapture.original R hG N (s j) p J u (Classical.arbitrary I)
    (weight C 0 j) (fun i=>a i j) (snap C j p o) stop.live.1 us hN sj.le d Y L.system L.literal (cuts 0)
    L.tabs stop.live u (stop.doors 0).post le_rfl (stop.doors p) ref money pos old zero fit spaced (hy.pos j)
    (hup j) (Or.inr (fun k _ h=>hprice j k h.le)) _ (fun _=>rfl) (fun i=>ins i (Y i)) unit hzj le_rfl
    (weight_pos C 0 j) board.1 (le_refl (E j)) board.2
  exact main.trans good

end YM.Integration.WilsonOriginalTwoFlatGridCapture
end
