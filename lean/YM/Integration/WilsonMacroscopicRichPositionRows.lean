import YM.Integration.WilsonMacroscopicRichTwoDatePivot

/-! The physical two-point row and its full clustered Wilson observation use exactly the same appointed far field and smooth profile. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichPositionRows
open Filter Function Set Lattice Wilson RG Source Extraction Table Spec RG17 Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register OPE OPE.Orbits
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichTwoDatePivot WilsonMacroscopicRichSignedAmplitude
open private companion from YM.Integration.WilsonMatrixTicketLanesNormalizedPivot
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}{n h:ℕ}
    (F:Spec.Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)

abbrev Seats := Exterior (standard R.family.book.grid)
abbrev Atom (h:ℕ):=(standard R.family.book.grid).Ref h

def profile (e:Seats (R:=R))(w:Atom (R:=R) h)(eq:e=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h w)(φ:Test (e.n+1)):Test 2 :=
  cast (congrArg (fun t:Seats (R:=R)=>Test (t.n+1)) eq) φ

theorem output (e:Seats (R:=R))(w:Atom (R:=R) h)(eq:e=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h w)(φ:Test (e.n+1))
    {τ:ℝ}(tp:0<τ)(y:S.Field h):WilsonMatrixTicketLanesSmearedRows.observation F J Z e φ τ h y =
    (profile e w eq φ).applyTo (fun z=>S.read (τ•z) (Fin.cons ⟨h,S.representative h y⟩ (fun _:Fin 1=>
       ⟨h,S.representative h (homogeneous F J Z τ h ((Bel R.family.book).project h w))⟩))) :=by
  subst e
  rw [WilsonMatrixTicketLanesSmearedRows.on_field F J Z _ φ tp y]
  rfl

def sample (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)
    (issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j))
    {τ:ℝ}(tp:0<τ)(r:ℝ)(x:Points n)(v:Fin n→(Bel R.family.book).Tag)(j:B.probes.index):ℂ:=
  reading J (profile (B.probes.shell j) (w j) (issued j) (test B j)) tp
    ⟨h,active F J Z τ h ((Bel R.family.book).project h (w j))⟩ r x v

theorem far (B:Profiles R h)(w:B.probes.index→Atom (R:=R) h)(τ:ℝ)(j:B.probes.index):
    J τ h (active F J Z τ h ((Bel R.family.book).project h (w j)))=
    homogeneous F J Z τ h ((Bel R.family.book).project h (w j)):=by
  simp only [active,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]

theorem signed {Y:(Bel R.family.book).Hierarchy}(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)(h:ℕ):
    ∃B:Profiles R h,∃w:B.probes.index→Atom (R:=R) h,∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∃C:ℝ,0≤C ∧ ∀g:ℝ→ℝ,Coupling G g→∀k:ℕ,∀ᶠr in trail,
      let τ:=r/(g r)^k
      ∃tp:0<τ,∀n:ℕ,∀x:Points n,∀v:Fin n→(Bel R.family.book).Tag,∀y y':S.Field h,
        let signal:=sample F J Z B w issued tp r x v
        (g r)^(k*(h+1))*‖(J r h).symm (y-y')‖ ≤ C*(‖row F J Z B τ y-signal‖+‖signal-row F J Z B τ y'‖):=by
  obtain ⟨B,two,payment⟩:=WilsonMacroscopicRichTwoDatePivot.original F J Z lead owed simple h
  choose w issued using two
  obtain ⟨C,cp,decoder⟩:=payment 1 zero_lt_one
  refine ⟨B,w,issued,C,cp,?_⟩
  intro g hg k
  let dates (r:ℝ):=r/(g r)^k
  have rate:=length_rate.div ((coupling_rate hg simple).power k)
  have tst:Tendsto dates trail trail:=tendsto_nhdsWithin_iff.mpr ⟨rate.tends (by simp only [mul_zero,sub_zero];norm_num) to_log_zoom,rate.pos⟩
  filter_upwards [tst.eventually decoder,hg.positive,length_rate.pos,(hg.conforms simple).eventually (gt_mem_nhds zero_lt_one)] with r accepts gp rp low
  intro τ
  have power:0<(g r)^k:=pow_pos gp k
  have full:0<(g r)^(k*(h+1)):=pow_pos gp _
  have tp:0<τ:=div_pos rp power
  have eq:(g r)^k*τ=r:=by change (g r)^k*(r/(g r)^k)=r;field_simp [power.ne']
  have sg: (g r)^k∈Ioc (0:ℝ) 1:=⟨power,pow_le_one₀ gp.le low.le⟩
  have invert:((g r)^k)^(-(h:ℝ)-1)=((g r)^(k*(h+1)))⁻¹:=by
    rw [show -(h:ℝ)-1=-((h+1:ℕ):ℝ) by push_cast;ring,Real.rpow_neg power.le,Real.rpow_natCast,pow_mul]
  refine ⟨tp,?_⟩
  intro n x v y y' signal
  have cost:=accepts _ sg (y-y')
  rw [eq,invert,(row F J Z B τ).map_sub] at cost
  have pay:(g r)^(k*(h+1))*‖(J r h).symm (y-y')‖≤C*‖row F J Z B τ y-row F J Z B τ y'‖:=by
    calc _ ≤(g r)^(k*(h+1))*(C*((g r)^(k*(h+1)))⁻¹*‖row F J Z B τ y-row F J Z B τ y'‖):= mul_le_mul_of_nonneg_left cost full.le
         _=C*‖row F J Z B τ y-row F J Z B τ y'‖:=by field_simp [full.ne']
  exact pay.trans (mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub _ signal _) cp)
end YM.Integration.WilsonMacroscopicRichPositionRows
