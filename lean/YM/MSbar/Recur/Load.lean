import YM.MSbar.Recur.Read
import YM.MSbar.Diagram.Frost
/-! Vacuum RG contributions. Elastic BRST rows preserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play
open Diagram.WardOps Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Crest Deck
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{P R D Q: Sites C}{c d e k:Bit}{f g:Functionals C}{z:ℂ}{r s t:ℝ}
variable (h:Window W k r P)(hk:e=k+d)

-- avoid transporting parity equality within maps from terms; specialize to d' strength by proof argument
namespace Work
lemma down (h: Pilot univ 0 W k (liftS P))(U:Set ℂ) : Pilot U 0 W k (liftS P):=
   ⟨fun a b=> (h.cost a b).upon (subset_univ _),fun a b he _ _=> h.parity a b he _ (mem_univ _),fun a b z _=> h.uniformL a b z (mem_univ _),fun a b z _=> h.uniformR a b z (mem_univ _)⟩
include h hk
omit hk in
lemma here (U:Set ℂ): Band U (liftS P) r:= fun _ _=> h.bounded _ (mem_univ _)

def loop : Mono W d e:= fun z=> {
 toFun:= fun x=> ⟨traceP W z P x.val, hk ▸ (Live.gets z x.property h)⟩
 map_add':=fun x y=> Subtype.ext (Live.line_sum z x.property h y.property)
 map_smul':=fun c x=> Subtype.ext (Live.mass z x.property h c)}
-- need include h hk before signature?
lemma loop_val (x:Deck W d)(z:ℂ):(loop h hk z x).val=traceP W z P x.val:= rfl
lemma aligns (hf:Live W d (f z)): Play.post (loop h hk) f z= Lap W (liftS P) f z:= by rw [Play.post,loop_val, plug_eq hf, atP]
lemma lin : Play.Linear (loop h hk):=by
    intro U HU X H; apply Full.congr (F:= Lap W (liftS P) X) ?_ Profit.pub (fun z hz=>Eq.symm (aligns h hk (H.freeze hz)))
    rw [hk]; exact (payload H (down h.fit U) (here h U) h.space Profit.pub).rechoose Profit.proper _
omit hk
variable {l:Bit} (hh:l=k+d+e)
include hh
def tree : Poly W d e l := fun z=> LinearMap.mk₂ ℂ (fun x y=> ⟨traceT W d z P x.val y.val, hh ▸ Live.wins z x.property h y.property⟩) (fun _ _ _=> Subtype.ext (Static.plus_T z)) (fun c _ _=> Subtype.ext (Static.scale_T z c)) (fun _ _ _=> Subtype.ext (Static.plus_T' z)) (fun c _ _=>Subtype.ext (Static.scale_T' z c))
lemma tree_val (x y)(z:ℂ): (tree h hh z x y).val=traceT W d z P x.val y.val:=rfl
lemma true_tree (hf:Live W d (f z))(hg:Live W e (g z)): Play.twin (tree h hh) f g z = splice W d (liftS P) f g z := by rw [Play.twin,tree_val,plug_eq hf,plug_eq hg,atT]
lemma poly : Polarized (tree h hh):=by
    intro U HU X Y hx hy; refine Full.congr ?_ Profit.pub (fun z hz=> Eq.symm (true_tree h hh (hx.freeze hz) (hy.freeze hz))); rw [hh]; exact spin_splice hx hy (down h.fit U) (here h U)
omit hh h
variable (hQ:Pilot univ 0 W k (liftS Q))
include hQ hk
def arrow : Mono W d e:= fun z=>{toFun:=fun x=> ⟨traceR W z Q x.val,hk ▸ Live.hits z x.property hQ⟩,map_add':=fun _ _=>Subtype.ext (Static.plus_R z),map_smul':= fun c _=> Subtype.ext (Static.scale_R z c)}
lemma arrows (x:Deck W d): (arrow hk hQ z x).val= traceR W z Q x.val:= rfl
lemma true_arrow (hf:Live W d (f z)): Play.post (arrow hk hQ) f z= Arrow.tick W (liftS Q) f z := by rw [Play.post,arrows,plug_eq hf,atR]
lemma actual : Linear (arrow hk hQ) := by intro U HU X hx; refine Full.congr ?_ Profit.pub (fun z hz=> Eq.symm (true_arrow hk hQ (hx.freeze hz))); rw [hk]; exact Arrow.full hx (down hQ U)
end Work
end YM.MSbar.Play
