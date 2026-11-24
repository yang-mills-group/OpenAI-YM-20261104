import YM.Integration.WilsonOriginalPublicFigurePosition

/-! The registered cutoff vectors in the finite position frame, at the true
planting and reporting spacings. Each original angular leg retains its unit
and all of its lower engineering components. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 450000
namespace YM.Integration.WilsonOriginalPublicFigureProjected
open Finset Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato PowerSeries
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Book MS.Book.Program OPE RegulatorIR.FVAAlt2
open WilsonOriginalMicroscopicGuardedPageSchool (Indexed)
open WilsonOriginalPublicTrialInput (vector salary)
open WilsonMaxwellThermometerChargedHeads (sector arm)
open WilsonMaxwellThermometerPositionCurrency (received physicalWord)
open WilsonOriginalPublicFigurePosition (booked clock)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n h d:ℕ}

def change (X:Sample n)(a:ℝ)(h:ℕ):Sec G h→ₗ[ℂ]Sec G h:=
  ∑j:Fin (h+1),((X.F.spacing:ℂ)^j.val/(a:ℂ)^h) •
    ((en (G:=G) (Nat.le_of_lt_succ j.isLt)).comp (Normalize.part h j.val))

theorem changed (X:Sample n)(a:ℝ)(p:Sec G h):
    change X a h p=received X a p:=by
  simp only [change,received,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]

def dose (F:Labels.Frame G h)(high:h≤d)(X:Sample n)(a:ℝ):F.Coeff→ₗ[ℂ]Sec G d:=
  (up high).comp ((change X a h).comp (sector F))

theorem occupied (F:Labels.Frame G h)(high:h≤d)(X:Sample n)(a:ℝ)(v:F.Coeff):
    dose F high X a v=∑i,v i • up high (received X a (arm F i)):=by
  simp only [dose,LinearMap.comp_apply,WilsonMaxwellThermometerChargedHeads.summed,map_sum,map_smul,changed]

theorem deposited (W:Initialize G)(F:Labels.Frame G h)(high:h≤d)(X:Sample n)(a:ℝ)
    (v:F.Coeff)(o:X.F.Sites):
    regal W d X o (dose F high X a v)=physicalWord W X a (sector F v) o:=by
  rw [dose,LinearMap.comp_apply,LinearMap.comp_apply,change,LinearMap.sum_apply,map_sum]
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,map_smul]
  rw [map_sum,physicalWord,Finset.smul_sum]
  apply sum_congr rfl
  intro j _
  rw [map_smul,show up high (en (Nat.le_of_lt_succ j.isLt) (part h j.val (sector F v)))=
      en ((Nat.le_of_lt_succ j.isLt).trans high) (part h j.val (sector F v)) from rfl,regals,
      Initialize.atSite,LinearMap.smul_apply,smul_smul]
  congr 1
  have nonzero:(X.F.spacing:ℂ)≠0:=Complex.ofReal_ne_zero.mpr X.F.positive.ne'
  field_simp [nonzero]

variable (R:Run G)(g j:Fin 3→ℕ)(K target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (g a))(before:∀a,j a≤K)(registered:Indexed R g j target η M Y)
local notation "F" i:max => R.family.labels.level (g i)

def trial (N per:ℕ)(f:Fin n→Fin 3)(hi:∀i,g (f i)≤d)(X:Sample n):Tags G d n:=
  fun i=>dose (F (f i)) (hi i) X (R.family.S.a K)
    (vector R g j K target η M Y before registered N per (f i))

def planting (R:Run G)(m K per:ℕ):Mesh:=
  WilsonSeparatedOriginalThermometerDetectorMesh.chart R K per (R.family.S.a K/R.family.S.a m)
    (div_pos (R.family.S.a_pos _) (R.family.S.a_pos _))

theorem physical (W:Initialize G)(N per m:ℕ)(f:Fin n→Fin 3)(hi:∀i,g (f i)≤d)
    (sites:pack n)(center:Four ℝ)(s:Finset (Fin n)):
    let X:Sample n:=⟨planting R m K per,sites,center⟩
    let v:=vector R g j K target η M Y before registered N per
    numberA W d X (trial R g j K target η M Y before registered N per f hi X) s=
      Bare.normalized _ G (∏i∈s,physicalWord W X (R.family.S.a K)
        (sector (F (f i)) (v (f i))) (chartV X i)):=by
  intro X v
  simp only [numberA,trial,deposited,v]

theorem original (W:Initialize G)(V:Store G)(d:ℕ):
    ∀ᶠ mesh in Front,∀(team:ℕ→Plan)(θ:ℝ),
    let Z:=Normalize.deck ((V.survey d).Lays (V.prepared d) (clock team θ (batch W mesh d)))
    ∃B:Guard G d,Formal B ∧ Z*B=1 ∧ B*Z=1 ∧
      (∀q,coeff q B (leaf G d)=if q=0 then leaf G d else 0) ∧
      ∀N per (f:Fin n→Fin 3)(hi:∀i,g (f i)≤d)(sites:pack n)(center:Four ℝ)
        (φ:Test n)(s:Finset (Fin n)),
      let X:Sample n:=⟨mesh,sites,center⟩
      let p:=trial R g j K target η M Y before registered N per f hi X
      YM.FVAAlt2.Lobby.redo team θ (said (batch W mesh d) φ (missing p s))=
        ∑b:Fin n→Dime G d,said (booked V W mesh d team θ) φ (fun i=>dime G d (b i))*
          ∏i,tax B (missing p s i) (b i):=by
  filter_upwards [WilsonOriginalPublicFigurePosition.original V W d] with mesh funded
  intro team θ Z
  obtain ⟨B,legal,zb,bz,unit,_,read⟩:=funded team θ
  exact ⟨B,legal,zb,bz,unit,fun _ _ _ _ _ _ φ s=>read _ φ _ s⟩

end YM.Integration.WilsonOriginalPublicFigureProjected
end
