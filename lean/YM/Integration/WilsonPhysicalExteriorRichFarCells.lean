import YM.Integration.WilsonPhysicalExteriorSampledGram
import YM.Integration.WilsonPhysicalExteriorSmearedWindow

/-! Original independently marked finite R-rich fields on the precise integer
sites of the centered far detector. Translation of the continuum field uses
the original interacting MS spatial law, including its true signed vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorRichFarCells
open Function Filter Set Finset Real Lattice MeasureTheory Pert Pert.Position RG RG16
open XSpace XSpace.Cirrus XSpace.Structure1 FVA2 FVA2.Register MS MS.Land MS.Menus MS.Logarithm MS.Rake MS.Tone MS.Tide MS.Dial
open PhysicalNext.Repeat.Legato FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open WilsonPhysicalExteriorQuadratureClock WilsonPhysicalExteriorCompactWindow WilsonPhysicalExteriorFirstCut
open WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorFirstCutScale
open scoped Topology BigOperators Classical
variable {n:ℕ} {G:Gauge}
variable (R:Run G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (Q:Prescription (Press.portDeck G))
local notation "B₀" => Press.portDeck G
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "θ" => WilsonPhysicalExteriorActualSides.time R
local notation "T₀" => WilsonPhysicalExteriorFirstCutScale.ratio R

def away (i:Fin (n+1)) : Bool:=decide (i≠0)
def relative (z:Points (n+1)) (i:Fin (n+1)) : QP:=Fountain.metric z i-Fountain.metric z 0
def offset (v:Sample (n+1)) (i:Fin (n+1)) : Cover:=v.layout i-v.layout 0

private theorem centered (v:Sample (n+1)) (i:Fin (n+1)) :
    relative (familiar v) i=v.F.spacing • Tone.embed (offset v i) := by
  ext a
  change v.F.spacing*(v.layout i a:ℝ)-v.center a-(v.F.spacing*(v.layout 0 a:ℝ)-v.center a)=
    v.F.spacing*(((v.layout i a-v.layout 0 a:ℤ)):ℝ)
  push_cast;ring

theorem index (c c':ℝ) (s:Bool) (j per:ℕ) (v:Sample (n+1)) (hv:v.F=grid R c c' true s (j,per))
    (i:Fin (n+1)) :
    positions R c c' away (relative (familiar v)) i j=offset v i := by
  funext a
  by_cases hi:i=0
  · subst i; simp [away,relative,zoom,positions,Dial.assign,offset]
  · have yes:away i=true:=by simpa only [away,decide_eq_true_eq] using hi
    have hp:=congrFun (centered v i) a
    rw [hv,outer_spacing] at hp
    simp only [positions,Dial.assign,Nat.cast_zero,exp_zero,one_mul,yes,zoom,if_true,Pi.smul_apply,smul_eq_mul]
    rw [hp]
    change ⌊exp (θ c j)*(T₀ c' j*(exp (-(θ c j))/T₀ c' j*((offset v i a:ℤ):ℝ)))⌋=_
    rw [exp_neg]
    have pos:0<T₀ c' j:=exp_pos _
    field_simp [pos.ne',(exp_pos (θ c j)).ne']
    exact Int.floor_intCast _

def cell (D:Fin (n+1)→Label B₀) (c:ℝ) (side:Bool) (u:ℝ) (k j per:ℕ) (v:Sample (n+1)) : ℂ:=
  Lobby.evaluateR R.metals.O (RegulatorIR.FVAAlt2.Lodge.basisR R) Q D
    (scene R c (fun i _=>offset v i) side 0) u k (j,per)

private theorem location (c c':ℝ) (s:Bool) (j per:ℕ) (v:Sample (n+1)) (hv:v.F=grid R c c' true s (j,per)) :
    testP (field R c 0 (fun i _=>offset v i)) (j,per)=fun i=>T₀ c' j • relative (familiar v) i := by
  funext i
  rw [centered,hv,outer_spacing,smul_smul]
  change exp (-(θ c j)) • Tone.embed (offset v i)=
    (T₀ c' j*(exp (-(θ c j))/T₀ c' j)) • Tone.embed (offset v i)
  congr 1;field_simp [(show 0<T₀ c' j from exp_pos _).ne']

private theorem moving (D:Fin (n+1)→Label B₀) (u s:ℝ) (k:ℕ) (z:Points (n+1)) (hz:z∈conf (n+1)) :
    MSExteriorDilation.moment M D (u+s) (Fountain.metric z) k=
      MSExteriorDilation.power (MSExteriorDilation.weight D) s*
      tour M D u (fun i=>exp s • relative z i) univ k := by
  have full:=MSExteriorDilation.scales M D (u+s) s (Fountain.metric z) (Fountain.metric_conf hz) k
  rw [add_sub_cancel_right] at full
  refine full.trans (congrArg (fun v:ℂ=>MSExteriorDilation.power (MSExteriorDilation.weight D) s*v) ?_)
  have inj:Injective (MSExteriorDilation.stretch s (Fountain.metric z)):=by
    intro i l h;apply Fountain.metric_conf hz;exact (smul_right_injective _ (exp_pos s).ne') h
  unfold MSExteriorDilation.moment tour book
  rw [Arrival.Schedule.transfers u D M (x:=MSExteriorDilation.stretch s (Fountain.metric z))
    (y:=fun i=>exp s • relative z i) inj (fun i l=>by
      simp only [MSExteriorDilation.stretch,relative,←smul_sub];congr 1;abel)]

private theorem date (D:Fin (n+1)→Label B₀) (c:ℝ) (s:Bool) (W:Fin (n+1)→ℕ→ Cover)
    (k:ℕ) (u:ℝ) (j per:ℕ) :
    signed R M Q D c W s k u (j,per)=signed R M Q D c (fun i _=>W i j) s k u (j,per) := by
  cases s <;> rfl

private theorem evaluation (D:Fin (n+1)→Label B₀) (c:ℝ) (s:Bool) (v:Sample (n+1))
    (k:ℕ) (u:ℝ) (j per:ℕ) :
    signed R M Q D c (fun i _=>offset v i) s k u (j,per)=
      cell R Q D c s u k j per v-tour M D u (testP (field R c 0 (fun i _=>offset v i)) (j,per)) univ k := rfl

private theorem held (D:Fin (n+1)→Label B₀) (c c':ℝ) (s:Bool) (j per:ℕ)
    (v:Sample (n+1)) (hv:v.F=grid R c c' true s (j,per)) (k:ℕ) (u:ℝ) :
    signed R M Q D c (positions R c c' away (relative (familiar v))) s k u (j,per)=
      cell R Q D c s u k j per v-tour M D u (testP (field R c 0 (fun i _=>offset v i)) (j,per)) univ k := by
  let W:=positions R c c' away (relative (familiar v))
  have h: (fun (i:Fin (n+1)) (_k:ℕ)=>W i j)=(fun (i:Fin (n+1)) (_k:ℕ)=>offset v i):=by funext i l;exact index R c c' s j per v hv i
  exact (date R M Q D c s W k u j per).trans
    ((congrArg (fun Z=>signed R M Q D c Z s k u (j,per)) h).trans (evaluation R M Q D c s v k u j per))

/-- Every signed finite R-rich word has the specified independent continuum
MS reading at its exact far-mesh cell, after all field weights and the
desired engineering inversion charge. -/
theorem physical {hG:G.Simple} (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (D:Fin (n+1)→Label B₀) (K:Set (Points (n+1))) (non:Nonempty K) (legal:K⊆conf (n+1))
    {A δ:ℝ} (ha:0<A) (hd:0<δ) (size:∀z∈K,∀i,‖relative z i‖≤A)
    (split:∀z∈K,∀i l:Fin (n+1),i≠l→δ≤‖Fountain.metric z i-Fountain.metric z l‖)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀s:Bool,∀per≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      ∀v:Sample (n+1),v.F=grid R c c' true s (j,per)→familiar v∈K→
      let τ:=log (T₀ c' j)
      let err:=fun u:ℝ=>(T₀ c' j)^h*
        ‖MSExteriorDilation.power (MSExteriorDilation.weight D) τ*cell R Q D c s u k j per v-
          MSExteriorDilation.moment M D (u+τ) (Fountain.metric (familiar v)) k‖
      err μ≤exp (-q*Λ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ j) := by
  letI : Nonempty K:=non
  let w:=MSExteriorDilation.weight D
  have buy:=WilsonPhysicalExteriorCompactWindow.measured R (hG:=hG) M Q rows D c c' away
    (fun z:K=>relative z.val) slow h₁ h₂ h₃ lo A δ ha hd (fun z=>size z.val z.property)
    (fun z i hi=>split z.val z.property i 0 (by simpa only [away,decide_eq_true_eq] using hi))
    (fun z i l ne _=>by
      have eq:relative z.val i-relative z.val l=Fountain.metric z.val i-Fountain.metric z.val l:=by unfold relative;abel
      rw [eq];exact split z.val z.property i l ne)
    μ q k (h+w)
  filter_upwards [buy] with j hj s per hp v hv hvK
  have p:=hj ⟨familiar v,hvK⟩ s per hp
  have pr:(0:ℝ)<T₀ c' j:=exp_pos _
  let τ:=log (T₀ c' j)
  have et:exp τ=T₀ c' j:=exp_log pr
  have normP:‖MSExteriorDilation.power w τ‖=(T₀ c' j)^w:=by
    rw [MSExteriorDilation.power,Complex.norm_real,Real.norm_of_nonneg (exp_pos _).le,Real.exp_nat_mul,et]
  have eq (u:ℝ) :
      (T₀ c' j)^h*‖MSExteriorDilation.power w τ*cell R Q D c s u k j per v-
        MSExteriorDilation.moment M D (u+τ) (Fountain.metric (familiar v)) k‖=
      (T₀ c' j)^(h+w)*‖signed R M Q D c (positions R c c' away (relative (familiar v))) s k u (j,per)‖:=by
    rw [moving M D u τ k (familiar v) (legal hvK),et,←mul_sub,norm_mul,normP,held R M Q D c c' s j per v hv k u,
      location R c c' s j per v hv,pow_add,mul_assoc]
  exact ⟨(eq μ).trans_le p.1,(eq (μ+R.family.S.scale j)).trans_le p.2⟩

end YM.Integration.WilsonPhysicalExteriorRichFarCells
end
