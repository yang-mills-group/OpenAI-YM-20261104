import YM.Integration.WilsonOriginalPublicRelativeGramNativeHearing
import YM.Integration.WilsonAddressedPublicWideMeasure
import YM.Integration.WilsonAddressedPublicPooledWidth
import YM.Integration.WilsonAddressedPublicPairFence

/-! Original finite correlated income at the narrow pooled measurement scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativePooledCards
open Filter Set Function Lattice Wilson RG Source OPE Extraction RG17 Table Spec Climb
open XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick MS MS.Menus MS.Land MS.Theater Local.Physical
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato Trace.Pilot PhysMS XSpace.Cirrus Pert.Asymptotics

open Set Filter Function Lattice Wilson RG Source OPE Extraction Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramBookedHeads (source)
open RG17 Spec Table Climb XSpace XSpace.Normalize XSpace.Structure1 Maxwell Maxwell.Wick
open Labels Cells GapsContact.Stamps Trace.Terrace Next.Rank Next.Rank.Station MergeProof.East Next.UVStress
open WilsonThermometerUnitFilingFourPoolShell (radius)
open WilsonOriginalPublicRelativeGramFreePanel (pointsAt named)
open WilsonOriginalPublicRelativeGramAddresses (ports)
open WilsonOriginalPublicRelativeGramReflectedLimit (entered ordered)
open WilsonOriginalPublicRelativeGramPins (cutoff)
open WilsonAddressedPublicHomeCard (exponent)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonAddressedPublicCardBooks (Housed)
open WilsonAddressedPublicSelfCards (fee width)
open scoped Topology Classical BigOperators

variable {G:Gauge}(B:Deck G)(h:ℕ)(a:Axis)(R:Run G)
    {f:Extraction.Order}{S:Table R.family.book}(F:Spec.Final R.family f S)
    (J:ℝ → tower S)(ℓ:Ultrafilter (ℕ×ℕ))(avoid:Finset E4){g:ℝ → ℝ}
    (Γ:WilsonViewerReportingGrid.Grid (ℓ:=ℓ) F h g)
    {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "I" => Glyph B h
local notation "P" => named R B h
local notation "c" => wilson z

theorem original (simple:G.Simple)(bliss:Bliss F ℓ z H)(reference:WilsonPrescription G)
    (lead:Leading F J)(bank:PostT R.family.path.levels)(slow:WilsonWindowReportingPace.Slow R.kit)
    (temperature:Coupling G g)(T:ℕ):
    ∃M:ℝ,1≤M ∧ ∀ {cap:ℕ}(seats:h≤cap)(room:ℝ → Prop)
      (books:(s:ℝ) → room s → Book F (l:=ℓ) H z cap T s),
    (∀ᶠs in trail,∃hs:room s,Housed F (books s hs))  → 
    let Y:=source B h R F J ℓ room seats books false
    ∀ᶠs in trail,∀j:I,∀ᶠw:ℕ×ℕ in f.fuse,
      ‖entered B h a R F ℓ avoid Γ Y (s,w) j j‖≤(M/(c s)^(exponent T h))^2:=by
  classical
  obtain ⟨A,ap,price⟩:=WilsonAddressedPublicCardCapacity.original F J reference simple bliss lead T h
  obtain ⟨W,wp,widths⟩:=WilsonAddressedPublicPooledWidth.original F simple bliss bank slow T
  let M:=1+A*(∑i:I,‖P i‖)
  have normsum:0≤∑i:I,‖P i‖:=Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  have mp:1≤M:=le_add_of_nonneg_right (mul_nonneg ap normsum)
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have positive:∀ᶠs in trail,0<s:=self_mem_nhdsWithin
  have fine:Tendsto (fun s=>R.family.S.a (Γ.date s)/s) trail (𝓝 0):=
    squeeze_zero' (positive.mono fun s sp=>(div_pos (R.family.S.a_pos _) sp).le) Γ.upper
      (by simpa using (temperature.conforms simple).pow 2)
  have roomLimit:Tendsto (fun s=>W*s*(c s)^2/s) trail (𝓝 0):=by
    have cv:Tendsto (fun s=>W*(c s)^2) trail (𝓝 0):=by
      simpa using (tendsto_const_nhds (x:=W)).mul ((link.conforms simple).pow 2)
    apply cv.congr'
    filter_upwards [positive] with s sp
    field_simp [sp.ne']
  have spots:=WilsonAddressedPublicPairAperture.original R trail Γ.date id (fun s=>W*s*(c s)^2)
    positive nhdsWithin_le_nhds fine roomLimit (fun _:Unit=>avoid) (fun _=>pointsAt a)
    (fun _=>WilsonAddressedPublicWideMeasure.distinct a)
  refine ⟨M,mp,?_⟩
  intro cap seats room books funded Y
  filter_upwards [funded,widths,price,spots,link.positive,positive,
    (show Tendsto id trail (𝓝 (0:ℝ)) from nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one),
    (link.conforms simple).eventually (gt_mem_nhds zero_lt_one)] with s live wall capital positions gp sp ss gs
  obtain ⟨hs,housed⟩:=live
  let house:=books s hs
  let day:Fin (cap+1):=⟨h,Nat.lt_succ_of_le seats⟩
  let home:=fun _:Bool=>house
  let v:=fun (_:Bool)(i:I)=>J s h (P i)
  let b:=fun (_:Bool)(_i:I)=>false
  let x:=fun _:Unit=>ports R avoid (pointsAt a) (Γ.date s) s
  have same:WilsonAddressedPublicPairPins.name R F home day v b=(fun _=>Y s):=by
    funext t w i
    simp only [Y,source,dif_pos hs]
    rfl
  intro j
  have ceiling:=wall house day (v false j)
  have lower:=positions ()
  let m:=width F house day (v false j) false
  have space:2*R.family.S.a (m-1)<‖R.family.S.gridPoint (Γ.date s) (x () 0)-R.family.S.gridPoint (Γ.date s) (x () 1)‖:=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left ceiling.2 (by norm_num)) lower.2
  have native:=WilsonAddressedPublicPairFence.original R F home day v b bank false j j (Γ.date s)
    x (fun _=>1) (by simpa only [WilsonAddressedPublicPairPins.whenFiled,min_self] using ceiling.1)
    (fun _=>lower.1) (fun _=>by simpa only [WilsonAddressedPublicPairPins.whenFiled,min_self] using space)
  rw [same] at native
  have unit:fee F house day (v false j) false*(c s)^(exponent T h)≤A*‖P j‖:=by
    simpa only [v,LinearEquiv.symm_apply_apply] using capital seats house housed (v false j) false
  have massive:‖P j‖≤∑i:I,‖P i‖:=Finset.single_le_sum (f:=fun i:I=>‖P i‖)
    (fun _ _=>norm_nonneg _) (Finset.mem_univ j)
  have capped:fee F house day (v false j) false≤M/(c s)^(exponent T h):=by
    apply (le_div_iff₀ (pow_pos gp _)).mpr
    exact unit.trans ((mul_le_mul_of_nonneg_left massive ap).trans (le_add_of_nonneg_left zero_le_one))
  have nn:0≤fee F house day (v false j) false:=by
    change 0≤dock (radius z T s)^T*GapsContact.Ascent.cost F h (radius z T s) (v false j)
    apply mul_nonneg _ (GapsContact.Ascent.cost_pos ..)
    apply pow_nonneg
    have positiveRadius:0<radius z T s:=mul_pos sp (pow_pos gp _)
    have smallRadius:radius z T s≤1:=(mul_le_of_le_one_right sp.le (pow_le_one₀ gp.le gs.le)).trans ss.le
    unfold dock Trace.Pilot.LogV
    rw [Real.log_inv]
    linarith [Real.log_nonpos positiveRadius.le smallRadius]
  filter_upwards [native] with w settled
  have paid:=settled a
  simp only [Fintype.sum_unique,norm_one,one_mul,WilsonAddressedPublicPairPins.cost] at paid
  exact paid.trans (by rw [pow_two];exact mul_self_le_mul_self nn capped)

end YM.Integration.WilsonOriginalPublicRelativeGramNativePooledCards
