import YM.OPE.Compatible.Lumen.Oriel
/-!
# actual first-order charge (always Feyn or standalone by appointed scope)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive Matrix
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} (H: Even n.val) (A:Alps B Q i l)
local notation "TK" => Keys G (Limb H)
lemma h_disc (h:G.Simple): Radial.Stationary (mural H A - fun _=> mural H A 0):=by
     have ht : fderiv ℝ (mural H A) 0=0:=by
          let f:=frameD A (n:=n); let L:=cloak H (G:=G)
          have ht : L 0=0:= L.map_zero; have hf : DifferentiableAt ℝ f 0:= ((A.fullK 1).plot n).differentiableAt (by simp); have hh: fderiv ℝ (f ∘ L) 0=0:=by
                rw [fderiv_comp _ (show DifferentiableAt ℝ f _ from ht.symm ▸ hf) L.differentiableAt,ht, show fderiv ℝ f 0=0 from dawnV A h]; rfl
          change fderiv ℝ (fun x=> (f ∘ L) x / 4) 0=0; simp_rw [div_eq_mul_inv]; rw [fderiv_mul_const ((show DifferentiableAt ℝ f (L 0) from ht.symm ▸ hf).comp _ L.differentiableAt),hh]; simp
     exact ⟨((muralD H A).of_le le_top|>.sub contDiffAt_const),by simp,fun u=> by unfold Radial.jet; rw [iteratedFDeriv_one_apply,fderiv_sub ((muralD H A).differentiableAt (by simp)) (differentiableAt_const _),ht,fderiv_const_apply]; simp⟩
structure Lit (b:ℝ) where
     s : Lid G (Limb H)
     uplift : s.f=ᶠ[𝓝 0] mural H A-(fun _=>mural H A 0)+hippie H
     light: s.w =ᶠ[𝓝 0] tintT H A b
namespace Lit
lemma lip (x:TK)(h:4 ≤ i): jet (mural H A-(fun _=> mural H A 0)+hippie H) 2 x = (boost H A.gear h B.K).P x x/2:=by
     unfold jet; rw [iteratedFDeriv_add_apply (show ContDiffAt ℝ ((2:ℕ):WithTop ℕ∞) (mural H A-fun _=> mural H A 0) 0 from ((muralD H A).of_le le_top).sub contDiffAt_const) ((hSm H).of_le le_top).contDiffAt,iteratedFDeriv_sub_apply ((muralD H A).of_le le_top) contDiffAt_const, iteratedFDeriv_const_of_ne (by decide)]; simp only [Pi.zero_apply,sub_zero, _root_.add_apply,mul_add]; rw [show _ * (iteratedFDeriv _ _ (hippie H) _) (fun _:Fin 2=>x)=_ from h_second H x]; exact mural_in H A x h
lemma buy (hx:4 ≤ i)(h:G.Simple)(b:ℝ): Nonempty (Lit H A b):=by
    let u:TK→ℝ:= mural H A-fun _=> mural H A 0; let f:= u+hippie H (G:=G)
    have ht:= ((muralD H A).sub (contDiffAt_const (c:=mural H A 0))).add (hSm H).contDiffAt; obtain ⟨X,hX,Hx⟩:=arcShape (f:=f) ht; have hy:=h_disc H A h
    obtain ⟨v,hv,hV⟩:=arcShape (tintD H A b)
    have hg: Radial.Stationary X:= by
         refine ⟨((ht.congr_of_eventuallyEq Hx).of_le le_top),?_,fun x=>?_⟩; rw [Hx.eq_of_nhds]; rw [show f 0= _ from (show f 0=u 0+ hippie H 0 from rfl),show u 0=0 from hy.base0,hZero, zero_add]
         have hl:= (h_station H (G:=G)).base1 x; unfold jet; rw [(Hx.iteratedFDeriv ℝ 1).eq_of_nhds]; unfold f; rw [iteratedFDeriv_add_apply (hy.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) ((hSm H).of_le le_top).contDiffAt,_root_.add_apply,mul_add,show _* (iteratedFDeriv _ _ (hippie H) _) (fun _ :Fin 1=>x)=0 from hl,add_zero]; exact hy.base1 _
    have hc:Cel X:=by
         obtain ⟨c,hc,h⟩:= (boost H A.gear hx B.K (G:=G)).slope
         refine ⟨c,hc,fun u=>?_⟩; rw [show jet X 2 u=jet f 2 u from congr_arg ((↑(Nat.factorial _) :ℝ)⁻¹ * ·) (DFunLike.congr_fun ((Hx.iteratedFDeriv ℝ 2).eq_of_nhds) _),show jet f 2 u= _ from lip H A u hx]; exact h _
    exact ⟨⟨⟨X,hg,hX,hc,v,lt_of_lt_of_eq (Real.exp_pos _) hV.eq_of_nhds.symm, ((tintD H A b |>.of_le le_top).congr_of_eventuallyEq hV),hv⟩,Hx,hV⟩⟩
end Lit
end YM.OPE.Cascade.Glass
