import YM.Integration.WilsonOriginalPublicRelativeGramNativePooledCards

/-! Genuine before-cutoff charge for the original outer arm on a compact reflected profile. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramOuterCards
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

open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonAddressedPublicPairPins (name)

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ → tower S)(Z:WilsonPrescription G)
    {ℓ:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
local notation "g" => wilson z

/-- One full homogeneous source vector per actual probe, at its own radius. -/
def actors {h D T:ℕ}{s:ℝ}(book:Book F (l:=ℓ) H z D T s)(seats:h≤D)
    {I:Type}(v:I → RG17.Free R.family h) (w:ℕ×ℕ)(j:I):R.family.label h:=
  ((book.rows ⟨h,Nat.lt_succ_of_le seats⟩).arm false (homogeneous F J Z s h (v j))).source w

/-- The input can include a different named determining atom at each detector sheet. -/
theorem original (simple:G.Simple)(bliss:Bliss F ℓ z H)(lead:Leading F J)
    (guard:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (bank:PostT R.family.path.levels)(slow:WilsonWindowReportingPace.Slow R.kit)
    {h:ℕ}{I:Type}[Fintype I](v:I → RG17.Free R.family h)(T:ℕ):
    ∃M:ℝ,1≤M ∧ ∀{τ:ℝ},0<τ  → 
      ∀ᶠs in trail,∀{D:ℕ}(seats:h≤D)(book:Book F (l:=ℓ) H z D T s),Housed F book  → 
      ∀(site:ℕ){L:Type}[Fintype L](u:L → Fin 2 → Cover)(μ:L → ℂ),
      (∀b,‖R.family.S.gridPoint site (u b 0-u b 1)‖≤1)  → 
      (∀b,τ*s≤‖R.family.S.gridPoint site (u b 0)-R.family.S.gridPoint site (u b 1)‖)  → 
      ∀ᶠp:ℕ×ℕ in f.fuse,∀j:I,∀a:Axis,
      ‖cutoff R a (fun _:I=>h) site u μ (fun _=>actors R F J Z book seats v) false p j j‖≤
        (∑b,‖μ b‖)*(M/(g s)^(exponent T h))^2:=by
  classical
  choose A ap feePaid using fun j:I=>WilsonAddressedPublicHomeCard.original F J Z simple bliss lead guard T h (v j)
  let M:=1+∑j:I,A j
  have mp:1≤M:=le_add_of_nonneg_right (Finset.sum_nonneg fun j _=>ap j)
  obtain ⟨W,wp,earlier⟩:=WilsonAddressedPublicPooledWidth.original F simple bliss bank slow T
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have positive:∀ᶠs in trail,0<s:=self_mem_nhdsWithin
  have heat:Tendsto (fun s=>(2*W)*(g s)^2) trail (𝓝 0):=by
    simpa using (tendsto_const_nhds (x:=2*W)).mul ((link.conforms simple).pow 2)
  refine ⟨M,mp,?_⟩
  intro τ hp
  filter_upwards [earlier,eventually_all.mpr feePaid,link.positive,
    (show Tendsto id trail (𝓝 (0:ℝ)) from nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one),
    (link.conforms simple).eventually (gt_mem_nhds zero_lt_one),positive,heat.eventually (gt_mem_nhds hp)]
    with s wall charges gp ss gs sp tiny D seats book housed site L fin u μ compact apart
  let day:Fin (D+1):=⟨h,Nat.lt_succ_of_le seats⟩
  let home:=fun _:Bool=>book
  let field:=fun (_:Bool)(j:I)=>homogeneous F J Z s h (v j)
  let branch:=fun (_:Bool)(_j:I)=>false
  apply eventually_all.mpr
  intro j
  have space:2*(W*s*(g s)^2)<τ*s:=by
    calc
      _=((2*W)*(g s)^2)*s:=by ring
      _<τ*s:=mul_lt_mul_of_pos_right tiny sp
  have row:=wall book day (field false j)
  have live:=WilsonAddressedPublicPairFence.original R F home day field branch bank false j j site u μ
    (by simpa only [WilsonAddressedPublicPairPins.whenFiled,min_self] using row.1) compact
    (fun b=>by
      simpa only [WilsonAddressedPublicPairPins.whenFiled,min_self] using
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left row.2 (by norm_num:0≤(2:ℝ))) (space.trans_le (apart b))))
  have earned:=charges j seats book housed false
  have large:A j≤M:=(Finset.single_le_sum (f:=A) (fun i _=>ap i) (Finset.mem_univ j)).trans
    (le_add_of_nonneg_left zero_le_one)
  have cap:fee F book day (field false j) false≤M/(g s)^(exponent T h):=
    (le_div_iff₀ (pow_pos gp _)).mpr (earned.trans large)
  have nn:0≤fee F book day (field false j) false:=by
    change 0≤dock (radius z T s)^T*GapsContact.Ascent.cost F h (radius z T s) (field false j)
    apply mul_nonneg _ (GapsContact.Ascent.cost_pos ..)
    apply pow_nonneg
    have rp:0<radius z T s:=mul_pos sp (pow_pos gp _)
    have one:radius z T s≤1:=(mul_le_of_le_one_right sp.le (pow_le_one₀ gp.le gs.le)).trans ss.le
    unfold dock Trace.Pilot.LogV
    rw [Real.log_inv]
    linarith [Real.log_nonpos rp.le one]
  filter_upwards [live] with p paid a
  exact (paid a).trans (mul_le_mul_of_nonneg_left (by rw [pow_two];exact mul_self_le_mul_self nn cap)
    (Finset.sum_nonneg (fun b _=>norm_nonneg (μ b))))

end YM.Integration.WilsonOriginalPublicRelativeGramOuterCards
