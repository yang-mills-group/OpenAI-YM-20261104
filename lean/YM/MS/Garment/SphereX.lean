import YM.MS.Garment.Packable
/-!
# The analytical BV grid Kernels

All order-n, though evaluation later in germs requires choose a finite horizon
 for the z-range (can truncate inputs). Ω always linearized on all kernels by linear
 extension granting analytic/massless quantities only for proper Sturdy false rows and Town.
 No pole prescription supplies this control. Kept independent. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Garment.Wave
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps
open Momentum Metric Color Book Convolve Signal Wick
open scoped Topology ContDiff
open Complex (I)
variable {G:Gauge}{x k:ℂ} (s:ℝ){F H:Mob G}
-- Δ linear extension by Axiom Free
lemma promoteZ (K:Rip G)(hk:Knot false K)(hv:x∈Town):∃ Ψ:MH (Mob G), ∀ F,Form0 false F→ Ψ F=ocean x K F:= by
    let M: Submodule ℂ (Mob G):={ carrier:=setOf (Form0 false), zero_mem':=Form0.zero, add_mem':=fun a b=> Form0.add a b, smul_mem':=fun x y h=> Form0.smul h x }
    let Ψ : M →ₗ[ℂ] Mob G:={ toFun F:= ocean x K F.val, map_add':=fun F H=> oceanR hk F.property H.property hv, map_smul':=fun c F=> scaleR hk F.property c }
    obtain ⟨Z,hx⟩:= Submodule.exists_isCompl M; refine ⟨Ψ.comp ( M.projectionOnto Z hx),fun f h=>?_⟩; let p:M:= ⟨f,h⟩; change Ψ ((M.projectionOnto Z hx) p.val)=_; rw [Submodule.projectionOnto_apply_left]; rfl
open Classical in
def port (x:ℂ)(K:Rip G): MH (Mob G) := if h: ∃ (Ψ:MH (Mob G)),∀ F, Form0 false F→ Ψ F=ocean x K F then h.choose else 0
lemma port_spec (hi:x∈Town)(K: Rip G)(hk: Knot false K)(hf:Form0 false F): port x K F=ocean x K F:= by classical exact (show port x K F=_ from by rw [port,dif_pos (promoteZ K hk hi)]; exact (promoteZ K hk hi).choose_spec F hf)

lemma Cert_all (G:Gauge): CountsD false (Q G) := ⟨fun n X _=> (Cert0 G).spin n X (fun h=> Bool.noConfusion h),fun h i b p=>(Cert0 G).wall h i b p⟩

variable (G k x)
def γ (x k:ℂ)(s:ℝ)(G:Gauge): GridR (Mob G) where
   J:= sweepQ (Q G)+k • port x (B0 G s)
   P:= k • port x (A0 G s)
   L:= k • port x (L0' G s)
   X:=squad (A0 G s)
   C:=squad (B0 G s)
   D:=squad (L0' G s)

variable {x G}
local notation "V" => γ x k s G
lemma Truss (H₀:x∈Town)(hp: Form0 false F) (h:Rock.sym F): (V).J ((V).P F)+ (V).L F= (V).P ((V).J F) := by
    let L:= port (G:=G) x; let U:= A0 G s; let K:= B0 G s; let Q:= Wick.Q G; obtain hv:Knot false K:= (B_caps ..).clearer; obtain he:Knot false U:= (A_caps ..).clearer
    change (sweepQ Q+k • L K) ((k • L U) F)+(k • L _) F=(k • L U) ((sweepQ Q+ k • L K) F); simp only [LinearMap.add_apply,LinearMap.smul_apply, map_add,map_smul]; -- parse
    unfold L; rw [port_spec H₀ U he hp, port_spec H₀ K hv hp, port_spec H₀ _ ((C_caps G s).clearer) hp, upcoming,upcoming,port_spec H₀ _ he ( Form0.portQ Q (Cert_all _) hp (count_caps G)),port_spec H₀ _ hv (torn H₀ hp he),port_spec H₀ _ he ( torn H₀ hp hv), lampLamp hp he (cl_a G s) hv (cl_b G s) h H₀]
    obtain hm:= qft hp he (cl_a G s) H₀ (count_caps _) (Cert_all G) ((C_caps ..).clearer) (cue G s); unfold Q; linear_combination (norm:=(simp only [smul_add]; abel)) (congr_arg (k • ·) hm) -- add smuls simpl
lemma quad0 (hz:x∈Town)(hp:Form0 false F)(hH:Form0 false H)(hf:Rock.sym F)(ht:Rock.sym H)(h0: tide F): (V).J ((V).X F H)+(V).D F H+ (V).C ((V).P F) H+ (V).C F ((V).P H)=(V).P ((V).C F H)+(V).X ((V).J F) H+(V).X F ((V).J H):=by
   let B:= B0 G s; let A:= A0 G s; have he := (A_caps G s).clearer; have hB:= (B_caps G s).clearer; obtain HK:= flightD hp he (cl_a _ _) hB (cl_b _ _) hH hf h0 ht hz (reverse_a G s) (reverse_b G s);
   have hv : portZ (Q G) (arbor A F H)+arbor (L0' G s) F H = arbor A (portZ (Q G) F) H+arbor A F (portZ (Q G) H):= by
       funext m; change ((Q G m).raise _) + tree _ (L0' G s m) _ _=_; rw [← cue]; exact axis_level (cl_a G s m) ( cue G s m|>.symm ▸ cl_c G s m) (ht m) (h0 m) (hf m)
   simp only [γ,LinearMap.add_apply,map_add,map_smul,LinearMap.smul_apply,schedule,upcoming]; simp_rw [port_spec hz _ hB (Form0.treed he (cl_a G s) (reverse_a G s) hp hH), port_spec hz _ he (Form0.treed hB ( cl_b G s) (reverse_b G s) hp hH),port_spec hz _ he hp,port_spec hz _ hB hp, port_spec hz _ he hH,port_spec hz _ hB hH]; unfold A at hv; linear_combination (norm:=(simp only [smul_add]; abel)) hv + congr_arg (k • ·) HK
end YM.MS.Garment.Wave
