import YM.MSbar.Diagram.Projection
-- Transfer operators, NOT prepared amplitudes. Identities in the common charge at every ε.
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram.Clear
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory Arrow
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {C:Type} {W:Edition C} {R T : ℝ} {m:ℕ} {F G : Functionals C} {D d k:Bit} {L P Q : Links C}
variable (h:Pilot univ 0 W 0 P) (hp:Band univ P R) (hr:0≤R) (H:Pilot univ 0 W k L) (he:Band univ L T) (ht:0≤T)
variable (V:Pilot univ 0 W k Q)

local notation "A" => Lap W P
local notation "B" => Lap W L
local notation "Pp" => splice W 0 P
local notation "Lp" => splice W 0 L
local notation "K" => tick W Q
include h hp hr H he ht
lemma on_loop (w:Full univ 0 W d F): A (B F)= B (A F):=by
    have ha:= payload w H he ht isOpen_univ; have hb:= payload w h hp hr isOpen_univ
    refine Total.identify (budget ha h hp hr isOpen_univ) (budget hb H he ht isOpen_univ) (fun i=>?_)
    obtain ⟨s⟩:=available i
    have hv : (i:ℂ)∈ univ:=mem_univ _
    rw [nominal ha h hp hr hv, nominal hb H he ht hv, nominal w H he ht hv, nominal w h hp hr hv]; exact Supported.straight s (Domain.supported h hp hv) (h.pace hv) (Domain.supported H he hv) (H.pace hv) (fares w.licensed hv) (w.quiet _ hv i) (w.span _ hv i)
lemma on_density (w:Full univ 0 W 0 F): A (Lp F F) + (2:ℂ) • Pp F (B F)= B (Pp F F)+(2:ℂ) • Lp F (A F):=by
    have ha:= payload w H he ht isOpen_univ; have hb:=payload w h hp hr isOpen_univ
    have G:= spin_splice w w H he; have L':=spin_splice w w h hp
    refine Total.identify ((budget G h hp hr isOpen_univ).add ((splice_total w ha h).scale _)) ((budget L' H he ht isOpen_univ).add ((splice_total w hb H).scale _)) (fun i=>?_)
    obtain ⟨s⟩:=available i;have hv : (i:ℂ)∈ univ:= mem_univ _
    simp only [Pi.add_apply,Pi.smul_apply]; rw [nominal G h hp hr hv, nominal L' H he ht hv]
    simp_rw [Tree.within,nominal w h hp hr hv,nominal w H he ht hv]; exact Supported.quadratic s (Domain.supported h hp hv) (h.pace hv) (Domain.supported H he hv) (H.pace hv) (fares w.licensed hv) (w.quiet _ hv i) (w.span _ hv i)
omit ht hr in -- line cost still control
lemma on_join (w:Full univ 0 W 0 F): Pp F (Lp F F)=Lp F (Pp F F):=by
    refine Total.identify (splice_total w (spin_splice w w H he) h) (splice_total w (spin_splice w w h hp) H) (fun i=>?_)
    obtain ⟨s⟩:=available i;have hv : (i:ℂ)∈ univ:= mem_univ _
    simp only [Tree.within]; exact Supported.triple s (Domain.supported h hp hv) (h.pace hv) (Domain.supported H he hv) (H.pace hv) (fares w.licensed hv) (w.quiet _ hv i) (w.span _ hv i)

omit h hp hr ht in
lemma on_pair (w:Full univ 0 W d F) (g:Full univ 0 W D G): splice W d L F G=sign d D • splice W D L G F:=by
    refine Total.identify (splice_total w g H) ((splice_total g w H).scale _) (fun i=> ?_)
    obtain ⟨s⟩:=available i; have hv:(i:ℂ)∈univ:= mem_univ _; simp only [Pi.smul_apply,Tree.within]; exact Supported.symmetry s (Domain.supported H he hv) (H.pace hv) (fares w.licensed hv) (w.quiet _ hv i) (fares g.licensed hv) (g.quiet _ hv i) (w.span _ hv i) (g.span _ hv i)

variable (hx : ∀ i:ℕ,L i i= Loops.shift (W.binary i) (W.members i) k (Q i i) (P i i))
include hx V
lemma on_current (w: Full univ 0 W d F): K (A F)- A (K F)=B F:=by
    have H' := full w V; have h':=payload w h hp hr isOpen_univ
    refine Total.identify ((Arrow.total h' V).sub (budget H' h hp hr isOpen_univ)) (budget w H he ht isOpen_univ) (fun i=>?_)
    obtain ⟨s⟩:=available i; have hv : (i:ℂ)∈univ:= mem_univ _
    simp only [Pi.sub_apply,lifts h' V hv, nominal w h hp hr hv,nominal H' h hp hr hv,nominal w H he ht hv,lifts w V hv]
    exact Supported.linear s (Domain.supported h hp hv) (h.pace hv) (Domain.supported H he hv) (H.pace hv) (transport w V hv) (fun a b=> (V.visit hv a b).1.continuous) (fares w.licensed hv) (w.quiet _ hv i) (hx i)
omit hr ht in
lemma on_leg (w:Full univ 0 W 0 F): K (Pp F F)= Lp F F+(2:ℂ) • Pp F (K F):=by
    refine Total.identify (Arrow.total (spin_splice w w h hp) V) ((splice_total w w H).add ((splice_total w (full w V) h).scale _)) (fun i=>?_)
    obtain ⟨s⟩:=available i; have hv:(i:ℂ)∈univ:=mem_univ _
    simp only [Pi.add_apply,Pi.smul_apply,lifts (spin_splice w w h hp) V hv,Tree.within,lifts w V hv]
    exact Supported.rate s (Domain.supported h hp hv) (h.pace hv) (Domain.supported H he hv) (H.pace hv) (transport w V hv) (fun a b=> (V.visit hv a b).1.continuous) (fares w.licensed hv) (w.quiet _ hv i) (hx i) (w.span _ hv i)
end YM.MSbar.Diagram.Clear
