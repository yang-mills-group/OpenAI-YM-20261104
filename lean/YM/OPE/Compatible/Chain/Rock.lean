import YM.OPE.Compatible.Chain.Canal
/-! # Pay tiles once, exact gauge state. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script
open PertExtension Series Asymptotics
variable {i:ℕ}{l:ℝ}{B:Sponsor G}{Q:Seasons B}
local notation "Lf" => Tested.germ
variable (H:Even n.val) (A:Alps B Q i l)
local notation "TK" => Libra.Keys G (Limb H)
structure Bor (b:ℝ) where
    f : TK→ℝ
    w : TK→ℝ
    u : f =ᶠ[𝓝 0] fun x=> mural H A x-mural H A 0
    t : w =ᶠ[𝓝 0] tintT H A b
    L (T:Plot H): Lid G T.Free
    acts (T:Plot H) : (L T).f=f ∘ T.rollX
    serves (T:Plot H): (L T).w= w ∘ T.rollX
lemma Bor.bought (h:G.Simple)(hx:4≤ i)(b:ℝ): Nonempty (Bor H A b):=by
     obtain ⟨f,hf,hs⟩:= arcShape ((muralD H A).sub (contDiffAt_const (c:= mural H A 0))) -- wrong
     obtain ⟨w,hw,hc⟩:= arcShape (tintD H A b)
     choose L H hL using fun T:Plot H=> bears_local H A h T hx b hs hf hc hw
     exact ⟨⟨f,w,hs,hc,L,H,hL⟩⟩
namespace Bor
variable {A H}{b:ℝ}{p:ChartRatio G} (R:LocalRatio p)
-- equation proof
lemma bodes (s:Bor H A b)(T U:Plot H){q:ScriptJ TK}(hp:(Pond H).Marbles q)(R:LocalRatio p): (s.L T).pay p (T.charted q)=(s.L U).pay p (U.charted q):=
     T.samePay U (tracksW H A b s.u s.t) (s.acts _) (s.acts _) (s.serves _) (s.serves _) hp R
lemma canonical (s:Bor H A b)(T:Plot H)(x: Libra.Keys G T.Free)(h:4 ≤ i): Radial.jet (s.L T).f 2 x = ((flatten (cloak H (T.rollX x))) ⬝ᵥ (tensor G (A.root.acts n)*ᵥflatten (cloak H (T.rollX x))))/8 := by
    let v:Keys G T.Free→L[ℝ] TK:= LinearMap.toContinuousLinearMap T.rollX; have hu: f s∘ v=ᶠ[𝓝 0] muralFace H A T-fun _=> mural H A 0:= s.u.comp_tendsto (v.map_zero ▸ v.continuous.tendsto 0)
    unfold Radial.jet; rw [s.acts]; change _⁻¹ * iteratedFDeriv ℝ 2 (f s ∘ v) 0 _= _; rw [(hu.iteratedFDeriv ℝ 2).eq_of_nhds,iteratedFDeriv_sub_apply ((mural_arc H A T).of_le le_top) contDiffAt_const]
    norm_num [iteratedFDeriv_const_of_ne]; rw [show (fun _ :Fin 2=>x)=![x,x] from funext fun i=> by fin_cases i <;>rfl,delta_arc H A T x x h];ring
end Bor
end YM.OPE.Cascade
