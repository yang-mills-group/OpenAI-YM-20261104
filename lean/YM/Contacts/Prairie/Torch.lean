import YM.Contacts.Prairie.Lease
noncomputable section
namespace YM.Contacts.Milling.Lumen
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Extension.UV.Linear
open Convoy Kale Ion Steam FreeResolvent
open scoped Topology BigOperators Classical Matrix NNReal ContDiff Matrix.Norms.Frobenius
variable {α : Type}{B : Bed}{n:Side}{G:Gauge}
lemma bright_room {η b:ℝ}{P:Clip}(h:∀ n,Floor B P n η b)(hp:∀ n,B.diagonal.acts n=1) : Blazing (flare G) B := by
   let U (n:Side):= hair (flare G) n; have ht (n) :=rootBase (G:=G) (h n) (hp n); refine ⟨flare_frame G, fun n=>⟨cradle_shape (flare_frame G),fun x=>?_⟩,fun n k i hi=>?_⟩
   · have hz:=fuel n 0 2 (G:=G) x; erw [if_pos (by decide),grate,if_pos (by decide), (ht _).2] at hz; exact hz
   let V:=wind (U n) (k+3) i; let p:= k+3-i; have he: AnalyticAt ℝ V 0:= wind_ana ..; have ht': Continuous V:= continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt)
   change Guards V p; by_cases h0:i=0; swap; · rw [show V=0 from funext fun x=> by unfold V wind; exact sum_eq_zero fun j _=> (fuel n i j x).trans (if_neg (fun u=> h0 u.1))]; exact ⟨continuous_const,analyticAt_const,fun _ _=>rfl,fun _ _=>rfl,by simpa only [Pi.zero_apply,sub_self] using (jet_bridge (f:=fun x:Swatch G n=>(0:ℝ)) (n:=p) analyticAt_const).2 (fun i j _=> jet_empty j i)⟩ -- p
   subst i; let E:= energy ∘ input G n; have hv : Pointwise E:= point_actual energy (starts _ Progress.Joint.energy_born.analyticAt (arm G n 1).toContinuousLinearMap) (fun a b=> energy_gauge b a) (fun a b=> energy_pull b a 0)
   have hh : Rays p (V-E) := valued p he hv.analytic (fun x i hi=> by unfold V U; rw [wind_jet,if_pos (by unfold p at *; omega),fuel]; split; rfl; symm; exact (jet_bridge hv.analytic).1 (rays_cast hv.analytic (ht n).1) x i (by omega))
   have hl (L:Link G n→L[ℝ]Link G n)(h:E ∘ L = E):V∘ (L:Link G n→Link G n)=V:= by
      apply instant (repeater (wind_controls ..) L) (wind_controls ..); let g:= merkin (he.sub hv.analytic) hh _ (L.analyticAt _) L.map_zero; convert g.sub hh using 1; ext x; change V (L x)-V x= V (L x)- E (L x)-(V x-E x); rw [show E (L x)=_ from congr_fun h x]; abel
   refine ⟨ht',he,fun u=> congr_fun (hl _ (funext fun x=> by unfold E Function.comp; rw [← stain_cons u x, energy_gauge])),fun s=> congr_fun (hl (orderTurn s) ?_), ?_⟩
   · ext x; change energy (input G n (flipCoords s ℝ x))=_; rw [← flip_links s,energy_pull]; rfl
   let P:= moveField (m:=n) (G:=G); let X:= ContinuousLinearMap.snd ℝ (BaseSites G n) (Link G n); let A:= (V-E) ∘ P; let C:= (V-E) ∘ X; have hp: Rays p (A-C):=(merkin (he.sub hv.analytic) hh _ moveField_analytic moveField_zero).sub (merkin (he.sub hv.analytic) hh _ (X.analyticAt _) X.map_zero)
   have hr : (A-C) =ᶠ[𝓝 0] fun a=>V (P a)-V a.2 := moveField_germ.mono fun a ha=> by
        have ht:E (P a)=E a.2:=(congr_arg Wilson.energy ha).trans (energy_gauge ..); change (V (P a) - E (P a)) - (V a.2-E a.2)=V (P a)-V a.2; rw [ht]; abel
   exact fun x=> (hp x).congr' ((along x).eventually hr) .rfl
end YM.Contacts.Milling.Lumen

end -- noncomputable? file Kindle didn't end?
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
def oil (F : bore G) := caravan e.Q (e.flag s) e.K F (e.Cov p s) (e.column (s::p)).metric
def port : Word → bore G
   | [] => flare G
   | s::p => let V:=e.oil p s (port p); lowerHouse (sink e.x V) V
abbrev kickoff := e.oil p s (e.port p)
@[simp] lemma origin : e.port []=flare G:=rfl
lemma pore : let U:=e.kickoff p s; e.port (s::p)= lowerHouse (sink e.x U) U:=rfl
lemma step_reserved (u:ℝ≥0) : ((2*u:ℝ≥0):ℝ)/s.L.val ≤ (u:ℝ):= by
   apply (div_le_iff₀ (side_pos _)).2; push_cast; rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg u); exact_mod_cast ((by decide:2≤3).trans s.prod)
variable {e p s} {S:Boom}
namespace License
variable (T:e.License S ζ)
include T
lemma down : ζ≤ (2:ℝ≥0)*ζ:= by simpa only [←two_mul] using (le_add_of_nonneg_right T.light.le : ζ≤ζ+ζ)
lemma warm : 2*( (2*ζ:ℝ≥0):ℝ) ≤ e.reach:= by
   push_cast; have ht:= NNReal.coe_le_coe.mpr T.lane; push_cast at ht; have he:= NNReal.coe_le_coe.mpr e.decade_le; push_cast at he; linarith only [ht,he, NNReal.coe_nonneg e.decade]
lemma blanket {F:bore G}{D:TableFee}(hs:s∈S)(ht:Blazing F (e.column p))(hu:Roof ζ F D): ∃ V:TableFee, Roof (2*ζ) (e.oil p s F) V ∧ Blazing (e.oil p s F) (e.column (s::p)):= by
   obtain ⟨b,hb,h⟩:=T.base s hs; have hv:=h p; let w:ℝ≥0:=2*ζ; have hw:0<w:=lt_of_lt_of_le T.light T.down; let k:=e.flag s; let x:= (e.column p).metric; have hz:= hv.direct; have hy : Row.strip (axisSky G k (e.A p s)) w (1+b):= sky_shape hv.feed hb; have hy':=e.awake p s; let V:= e.wheel p s; have hm:=strip_mono (e.K_funds (s::p)) T.warm le_rfl; have hc:= add_nonneg zero_le_one hb; exact ⟨_,upperroof w ζ e.Q V.V ht hy' V.governed hu (step_reserved ..) hz hy hb hc hm e.K_pos,restrung w ζ e.Q V.V ht hy' V.governed hu (step_reserved ..) hz hy hb hc hm e.K_pos hw e.valid⟩
lemma banks (h:OK S p): Aegis e.x (e.port p) (e.column p) ∧ ∃ V, Roof (2*ζ) (e.port p) V:= by
   induction p with
   |nil=>
    have hp:=flare_purse G (2*ζ); exact ⟨⟨bright_room (e.floor []) (e.top),fun i hi=> by rw [origin e,Lumen.flare, if_neg (by omega), salvia_zero],flare_even _,_,lt_of_lt_of_le T.light T.down,_,hp⟩, _,hp⟩
   |cons s p ih=>
     let U:=e.kickoff p s; obtain ⟨hp,V,H⟩:=ih h.tail; obtain ⟨W,ht,hV⟩:= T.blanket h.head hp.blazing ⟨fun i j=> (H.shelter ..).weaken (terrain_le T.down) le_rfl⟩; let y:= e.x; let w:=sink y U; have hq: Platinum U:= caravan_even hp.grade (e.Cov p s) (e.column (s::p)) e.Q; have he n := e.floor (s::p) n; let g:=lt_of_lt_of_le T.light T.down; obtain ⟨hh,h'⟩:= central_preserves y g hV (e.whole _) (he 1).starts (e.symmetry _) ht; let hx := budget_presage w ht; exact ⟨⟨hh,h',lower_even U w (sink_mast _) hq (sunk y U hq),_,g,_,hx⟩,_,hx⟩
lemma prosper (h:OK S p): Aegis e.x (e.port p) (e.column p):= (T.banks h).1
lemma signal (h:OK S p)(hs:s∈ S): ∃ V:TableFee, Roof (2*ζ) (e.kickoff p s) V ∧ Blazing (e.kickoff p s) (e.column (s::p)):= by obtain ⟨hp,V,H⟩:= T.banks h; exact T.blanket hs hp.blazing ⟨fun i j=> (H.shelter ..).weaken (terrain_le T.down) le_rfl⟩
end License
end Parcel
end
end YM.Contacts.Prairie
