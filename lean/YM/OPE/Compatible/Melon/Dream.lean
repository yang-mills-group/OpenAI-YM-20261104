import YM.OPE.Compatible.Melon.Stud
/-!
# Gaussian transport under color rotations; aimed at simple groups for averaging.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {H: Even n.val} (T: Plot H) {I:Type}
local notation "TK" => Keys G (Limb H)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
lemma rainbow_inj [Fintype I]{x y:Keys G I}(h:∀ a:Keys G I,rainbow a x=rainbow a y): x=y:=by
     apply sub_eq_zero.mp; apply rainbow_zero; have he:= h (x-y); let f:=x-y; change rainbow f f=0;rw [show rainbow f f= _ from (show rainbow f (x-y)=rainbow f x-rainbow f y from map_sub (ruby G I f) x y),sub_eq_zero]; exact he
lemma pool [Fintype I](v:G.El)(x y:Keys G I): rainbow (glint I v x) (glint I v y)=rainbow x y:=by
     let A: G.Color→ₗᵢ[ℝ] G.Color:= { G.adjoint v with norm_map':= G.norm_adjoint v }; exact Finset.sum_congr rfl fun i _=> A.inner_map_map _ _
lemma prayer (v:G.El)(x: TK): rinse H (glint _ v x)= glint _ v (rinse H x):=by
    apply rainbow_inj; intro a; obtain ⟨y,rfl⟩:= (glint _ v).surjective a
    rw [pool]; apply neg_inj.mp; unfold rainbow; rw [←tideDown,←tideDown]
    rw [show (Pond H).galaxy G (glint _ v y)=glint _ v ((Pond H).galaxy G y) from ?_]; exact pool ..
    ext1 p; exact (map_sub (G.adjoint v) _ _).symm
lemma qLinear (v:G.El)(x: TK): hippie H (glint _ v x)=hippie H x:=by unfold hippie; rw [prayer,pool]
lemma tollWind (v:G.El): (tall T ∘ glint _ v)=ᶠ[𝓝 0] tall T:=by
     filter_upwards [glow T v] with x hx; change hippie H _= _; rw [show layerZ T (glint _ v x)= _ from hx]; exact qLinear ..
lemma carriage (v:G.El)(u w: DK) : (fond H T G).P (glint _ v u) (glint _ v w) = (fond H T G).P u w:=by rw [fond_L,fond_L]; unfold chargeV; rw [gleam_p T,gleam_p T,prayer,prayer,pool]
lemma landSolo (x:FD)(p:DK)(h:rinse H (T.palmFrame G p +T.rollX x) = 0): landFuse H T G x=p:=by
     let y:=landFuse H T G x; apply sub_eq_zero.mp; by_contra ht; have hp:= chargedW H T (y-p) ht; have he := drains H T x; unfold certain at he; have hx : rinse H (T.palmFrame G (y-p))=0:= by
          rw [map_add] at h he; rw [map_sub, map_sub,show y= _ from rfl]; apply sub_eq_zero.mpr; exact add_right_cancel (he.trans h.symm)
     unfold chargeV at hp; rw [hx] at hp; simp [rainbow] at hp
lemma rises_at (v:G.El)(x:FD) : landFuse H T G (glint _ v x)=glint _ v (landFuse H T G x):=by
     let L:=glint (Limb H) v; apply landSolo; rw [gleam_p,←glint_roll, ← map_add,prayer,show rinse H _=0 from drains H T x, map_zero]
lemma rises_dir (x:FD)(y:DK)(v:G.El): compass H T G (glint _ v x,glint _ v y)=glint _ v (compass H T G (x,y)):=by
     change T.rollX _+T.palmL _ (landFuse H T G _) + T.palmL G _=glint _ v (T.rollX _+ T.palmL G _+T.palmL G _); rw [rises_at,← glint_palm,← glint_roll,← glint_palm, ← map_add, ←map_add]
lemma jet_R (k:ℕ)(x:TK)(v:G.El): jet (tall T) k (glint _ v x)=jet (tall T) k x:=by
     let L:= (glint (Limb H) v).toContinuousLinearEquiv.toContinuousLinearMap; unfold jet; have he:tall T ∘ L=ᶠ[𝓝 0] tall T:= tollWind T v; congr 1
     nth_rw 2 [←(he.iteratedFDeriv ℝ k).eq_of_nhds]; rw [Next.Foundations.jets_linear L ((tall_sane T).of_le (WithTop.coe_le_coe.mpr le_top))]; rfl
end YM.OPE.Cascade.Glass
