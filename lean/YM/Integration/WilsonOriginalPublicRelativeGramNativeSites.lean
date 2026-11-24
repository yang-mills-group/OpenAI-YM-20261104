import YM.Integration.WilsonOriginalPublicRelativeGramKineticMesh
import YM.OPE.Eye.Civic

/-! A genuine original f-grid translate at all K-branches and the named
independent mesh. The relative position keeps its actual physical scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeSites
open Filter Set Function WithLp Lattice Wilson RG Source OPE
open PhysicalNext.Repeat.Legato Extraction XSpace XSpace.Cirrus
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open scoped Classical Topology BigOperators

variable {G:Gauge}(R:Run G){n:ℕ}(W:Finset E4)(x:Points n)
local notation "a" => R.family.S.a

def center (M:Mesh):ℝ:=3*M.size/16

def shift (M:Mesh)(δ:ℝ):Cover:=fun _=>⌊center M/δ⌋

def bias (M:Mesh)(δ:ℝ):ℝ:=δ*(⌊center M/δ⌋:ℤ)-center M

def light:Points n:=points fun _=>WithLp.toLp 2 (fun _:Axis=>(1:ℝ))

def layout (M:Mesh){f K:ℕ}(live:f≤K)(s r:ℝ):Fin n→ Cover:=
  fun i=>OPE.zoom R.family.S live (ports R W x f r i+shift M (a f/s))

def sample (M:Mesh){f K:ℕ}(live:f≤K)(s r:ℝ):Sample n:=
  ⟨M,layout R W x M live s r,fun _=>center M⟩

theorem welcome_sample (M:Mesh){f K:ℕ}(live:f≤K)(s r:ℝ):
    welcome (sample R W x M live s r):=by
  constructor <;> intro i <;> dsimp [sample,center] <;> linarith [M.size_pos]

theorem rent (M:Mesh){δ:ℝ}(pos:0<δ): -δ≤bias M δ ∧ bias M δ≤0:=by
  have left:=mul_le_mul_of_nonneg_left (Int.floor_le (center M/δ)) pos.le
  have right:=mul_lt_mul_of_pos_left (Int.lt_floor_add_one (center M/δ)) pos
  have cancel:δ*(center M/δ)=center M:=by field_simp
  rw [cancel] at left right
  unfold bias
  constructor <;> linarith

theorem coordinates (M:Mesh){f K:ℕ}(live:f≤K){s r:ℝ}(sp:0<s)(rp:0<r)
    (metric:a K=s*M.spacing):
    familiar (sample R W x M live s r)=
      (r/s) • shape W x (a f/r)+bias M (a f/s) • (light:Points n):=by
  ext i u
  have e:=congrArg (fun v:E4=>v u) (OPE.zoom_grid (C:=R.family) live
    (ports R W x f r i+shift M (a f/s)))
  change a K*(layout R W x M live s r i u:ℝ)=
    a f*((ports R W x f r i+shift M (a f/s)) u:ℤ) at e
  rw [Pi.add_apply,Int.cast_add] at e
  change M.spacing*(layout R W x M live s r i u:ℝ)-center M=
    r/s*((a f/r)*(ports R W x f r i u:ℝ))+bias M (a f/s)*1
  rw [metric] at e
  dsimp only [bias,shift] at *
  field_simp [sp.ne',rp.ne'] at e ⊢
  linear_combination e

theorem original {Z:Type}{l:Filter Z}(M:Z→Mesh)(f K:Z→ℕ)(live:∀z,f z≤K z)(s r:Z→ℝ){gain:ℝ}
    (placed:∀ᶠz in l,0<s z ∧ 0<r z ∧ a (K z)=s z*(M z).spacing)
    (fine:Tendsto (fun z=>a (f z)/r z) l (𝓝 0))
    (relative:Tendsto (fun z=>r z/s z) l (𝓝 gain)):
    (∀z,welcome (sample R W x (M z) (live z) (s z) (r z))) ∧
    Tendsto (fun z=>familiar (sample R W x (M z) (live z) (s z) (r z))) l (𝓝 (gain • x)):=by
  have small:Tendsto (fun z=>a (f z)/s z) l (𝓝 0):=by
    have eqv:=fine.mul relative
    rw [zero_mul] at eqv
    apply eqv.congr'
    filter_upwards [placed] with z pos
    field_simp [pos.1.ne',pos.2.1.ne']
  have housing:∀ᶠz in l, -(a (f z)/s z)≤bias (M z) (a (f z)/s z) ∧
      bias (M z) (a (f z)/s z)≤0:=by
    filter_upwards [placed] with z pos
    exact rent (M z) (div_pos (R.family.S.a_pos _) pos.1)
  have blur:Tendsto (fun z=>bias (M z) (a (f z)/s z)) l (𝓝 0):=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using small.neg)
      tendsto_const_nhds (housing.mono fun _ hi=>hi.1) (housing.mono fun _ hi=>hi.2)
  have geometry:=WilsonOriginalPublicRelativeGramAddresses.limit W x
    (placed.mono fun z yes=>div_pos (R.family.S.a_pos _) yes.2.1) fine
  have total:=(relative.smul geometry).add (blur.smul_const (light:Points n))
  rw [zero_smul,add_zero] at total
  refine ⟨fun _=>welcome_sample ..,total.congr' ?_⟩
  filter_upwards [placed] with z pos
  exact (coordinates R W x (M z) (live z) pos.1 pos.2.1 pos.2.2).symm

end YM.Integration.WilsonOriginalPublicRelativeGramNativeSites
