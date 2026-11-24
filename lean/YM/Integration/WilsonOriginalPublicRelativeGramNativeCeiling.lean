import YM.Integration.WilsonOriginalPublicRelativeGramOrientationLimit

/-! The reflected Gram fixes one numerical ceiling before selecting the
cutoff, planting depth, independent frame, or approximating programme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramNativeCeiling
open Filter Set Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramOriented (maxwell)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator

variable {G:Gauge}(B:Deck G)(d:ℕ)(a:Axis)
local notation "Label" => Glyph B d
local notation "Frame" => Matrix Label Label ℂ

def Adequate (C:ℝ):Prop:=∀{Z:Type}{l:Filter Z}(A H:Z → Frame),
  Tendsto H l (𝓝 (maxwell B d a)) →
  Tendsto (fun z=>(A z)ᴴ*H z*A z) l (𝓝 (maxwell B d a)) →
  ∀ᶠz in l,‖A z‖≤C

theorem original:∃C:ℝ,0<C ∧ Adequate B d a C:=by
  let M:=maxwell B d a
  let readings:Frame×Frame → Frame×Frame:=fun z=>(z.2,z.1ᴴ*z.2*z.1)
  let l:=Filter.comap readings (𝓝 (M,M))
  have heard:Tendsto readings l (𝓝 (M,M)):=tendsto_comap
  have H:Tendsto Prod.snd l (𝓝 M):=(continuous_fst.tendsto _).comp heard
  have A:Tendsto (fun z:Frame×Frame=>z.1ᴴ*z.2*z.1) l (𝓝 M):=(continuous_snd.tendsto _).comp heard
  obtain ⟨C,cap⟩:=WilsonOriginalPublicRelativeGramOrientationLimit.bounded B d a Prod.fst Prod.snd H A
  refine ⟨max 1 C,zero_lt_one.trans_le (le_max_left ..),?_⟩
  intro Z k B₁ H₁ fit trace
  let rep:Z → Frame×Frame:=fun z=>(B₁ z,H₁ z)
  have fitted:Tendsto rep k l:=tendsto_comap_iff.mpr (fit.prodMk_nhds trace)
  exact (fitted.eventually cap).mono (fun _ yes=>yes.trans (le_max_right ..))

end YM.Integration.WilsonOriginalPublicRelativeGramNativeCeiling
