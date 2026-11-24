import YM.Contacts.Procession.Fauna
/-! # Real gauge contact bridge at all charge sectors. Hoist to harmonic frame.
Absorb every composition from earlier ranks at same charge. Uses no Ward-projection
shortcut replacing masks; statement concerns the actual formal calculations there.
-/
noncomputable section
namespace YM.Contacts.Procession.Hinges
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Welcome Resetter Shuttle.Tide Barrage Slope House
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
open Tree FreeResolvent Draw PhysicalNext.RankCovariance Catch
set_option autoImplicit false
variable {X Y A B ι κ α β: Type}{f m:Side} {G:Gauge}{n k i r l p:ℕ}{b c d:ℝ}
local notation "C" => (chart G)
lemma kin_stepL (A: Link G m→ℝ)(h:GuardsL A k)(hx:n<k)(H:Pulse.Rack (Lines G m 1))(hp:∀ i≤n,Poem (H i))(ht:∀ i≤n,∀ x, jet A i x=design (H i) x) (x: House.Dir (Co m (Candles G))):
    design (H n) (fderiv ℝ (dragged G m) 0 x)= design (H n) (bundleLink x)- ∑ j∈stops n, slew j*design ((C).folded j (H j.length)) x:= by
   have he : Rays k (A ∘ (chart G).stencil m - A ∘ bundleLink) := by
     rw [fixed]; exact merkin (f:=fun z:Swatch G m=> A (moveField z)-A z.2) ((AnalyticAt.comp (f:=moveField) (by rw [moveField_zero]; exact h.analytic) moveField_analytic).sub (h.analytic.comp (f:=Prod.snd (α:=BaseSites G m)) (x:=0) (contDiffAt_snd).analyticAt)) h.grade bundleSites ((bundleSites).analyticAt _) (map_zero _)
   have hA:= h.analytic; have hK:= congr_arg (fun F:House.Dir (Co m (Candles G))→Link G m=> fderiv ℝ F 0 x) (fixed (m:=m) G); have hw:= (nightwalk (AnalyticAt.comp (f:=(chart G).stencil m) (by rw [(C).zero_stencil]; exact hA) (C).analytic) (AnalyticAt.comp (f:=⇑(bundleLink (G:=G) (m:=m))) (by rw [map_zero]; exact hA) ((bundleLink).analyticAt _)) he n hx x); rw [Garf.woven hA, ht _ le_rfl, (C).metro A x _ hA hp ht,mul_sum] at hw; let p (j:OrderedFinpartition n):= (n.factorial:ℝ)⁻¹ * ((j.length.factorial:ℝ)*design ((C).folded j (H j.length)) x); let y:=OrderedFinpartition.atomic n; have hf j:p j=slew j*design ((C).folded j (H j.length)) x:= (mul_assoc ..).symm
   suffices he:p y=design (H n) (fderiv ℝ (dragged G m) 0 x) by rw [← hw, ← he]; simp_rw [← hf]; rw [eq_sub_iff_add_eq]; exact add_sum_erase _ p (mem_univ y)
   unfold p y; rw [(C).atom_form,hK]; exact inv_mul_cancel_left₀ (by positivity : (n.factorial:ℝ)≠0) _
lemma hoist_price [Fintype α][Fintype β] {L:Side}{P:Cross L α β}{σ η:ℝ≥0}{x:α}{F:Field (Fin n) (Node α)} (y:β)(h:P.strip η b)(ht:0≤b)(hq:(η:ℝ)/(L.val:ℝ)≤σ)(hv:Rest (terrain σ _) (0,x) F c): Rest (terrain η β) (0,y) (lifts P F) (access L η ( (0:Cover),x) ((0:Cover),y) * (c*(Fintype.card β*beamPrice η b)^n)):= by
    let D:= light_cost (u:=((0:Cover),y)) (influx hq) hv (fun _: Fin n=>ledgers h ht); simpa [lifts,hoist] using print_fee D
lemma pack_hoist [Fintype α][Fintype β] (R:Ratio m f){P:Cross R.count α β}{σ η:ℝ≥0}{F:Field (Fin n) (Node α)}{x:α}(h:P.strip η b)(y:β)(hp:0 ≤ b)(ht: (η:ℝ)/(R.count.val:ℝ) ≤ σ)(he:Rest (terrain σ _) (0,x) F c): packing (lower m) (lifts P F)= hoist (installed R P) (packing (lower f) F):= by
    unfold lifts hoist; rw [pack_print (light_cost (u:=((0:Cover),y)) (influx ht) he (fun _:Fin n=> ledgers h hp)), pack_hoist_aux (influx ht) he (fun _:Fin n=> ledgers h hp) (fun _=> st_new R P) ((0:Cover),y)] -- names
variable {H J:Bed}{P:Patch}{K:KernelChoices}{W: AtomBeam P}{z x:Dye G}
def mountain (G:Gauge)(σ:ℝ≥0)(B:ℕ→ℝ)(n:ℕ):= ∑ i∈stops n, ‖slew i‖ * ((∑ u,site_price (chart G) i σ u)*B i.length)
lemma mountain_fee {T:Pulse.Rack (Node (Dye G))}{s t:ℝ≥0}{B:ℕ→ℝ}(hx:s ≤ t)(hp:∀ i<n,Rest (terrain s _) (0,x) (T i) (B i))(y:Candles G): Rest (terrain s _) (0,y) (Slope.lottery n G T) (mountain G t B n):= Rest.sum (fun i hi=> (Hinges.blend_price (C) i y hx (hp _ (stops_lt n i hi))).smul _)
lemma mountain_pack {T:Pulse.Rack (Node (Dye G))}{s:ℝ≥0}{B:ℕ→ℝ}(hp:∀ i < n,Rest (terrain s _) (0,x) (T i) (B i))(y:Candles G)(m:Side): packing (lower m) (Slope.lottery n G T)= ∑ i∈stops n,slew i • (C).folded i (packing (lower m) (T i.length)):= by
   unfold Slope.lottery; rw [pack_sum (s:=stops n) (lower m)]; refine sum_congr rfl fun i hi=>?_ ; rw [smul_pack,pack_blend _ i y le_rfl (hp _ (stops_lt n i hi))]; intro i hi; exact ((blend_price (C) i y le_rfl (hp _ (stops_lt n i hi))).smul _).summ
lemma gauge_topo [Fintype α]{F X:Field (Fin n) (Node α)} (h: Summable F)(hm: Summable X)(he:Poem F)(hp:Poem X)(hg:∀ m, design (packing (lower m) F)= design (packing (lower m) X)) : F=X:= by
   funext y; have hw (m:Side): packing (lower m) F=packing (lower m) X:= unique_poem (poetic _ he _) (poetic _ hp _) (MvPolynomial.funext fun u=> congr_fun (hg _) u); apply tendsto_nhds_unique (portraying y h stepping); simp_rw [hw]; apply portraying _ hm stepping
variable {V:bore G}{S:Stairs G P.L}{s η t:ℝ≥0}{U:ℕ→ℝ}{v w:ℝ}

lemma gauge_horizon (hk : (η:ℝ)/P.L.val ≤ s)(ht:Awake G P K H J W v) (hp:Cabinet (brick G P K.penalty H) S)(hS:S.strip η b)(hb:0≤b)(hw:W.strip t c)(hw':η≤t)(hc:0≤c)(hu:(Origin.stretch P K G S).strip η w)(hu':0≤w)(hF: Mount V p)(hl:∀ i≤ n, Rest (terrain s _) (0,x) (coil V p l i) (U i)): let Z:=coil V p l; lifts (Origin.stretch P K G S) (Z n)=lifts (Origin.bleed G W) (Z n)-lifts (nest P G W) (Slope.lottery n G Z):= by
    intro Z; let A:= Origin.stretch P K G S; let B:= Origin.bleed G W; let Y:= nest P G W; let T (m:Side):=sprig P K m; let M (m:Side):Side:= m*P.L; let C':= Slope.lottery n G Z; let z:Candles G:= Sum.inr x; have hB:= bleed_strip (G:=G) (strip_mono hw (NNReal.coe_le_coe.mpr hw') le_rfl) hc; have hN:= succeeds (G:=G) hw hw' hc; have hY:0 ≤ spanned P t c:= spanned_positive hc; have hm:= mountain_fee (t:=s) (B:=U) le_rfl (n:=n) (fun i hi=>hl i hi.le) z; have hr:= hl n le_rfl;
    change lifts A (Z n)= lifts B (Z n)-lifts Y C'; refine gauge_topo (hoist_price x hu hu' hk hr).summ ((hoist_price x hB hc hk hr).summ.sub (hoist_price x hN hY hk hm).summ) hoist_shape (by rw [sub_eq_add_neg]; exact hoist_shape.add (Poem.minus hoist_shape)) (fun m=>?_)
    funext p'; let g:= (T m).ratio; let X':= installed g A *ᵥ p'; let B':= installed g B *ᵥ p'; let v:=installed g Y *ᵥ p'; have hx : X'= fderiv ℝ (dragged G (M m)) 0 v:= by
       let X'':= tensor G (extracted (T m) (planting g P.odd_side) (installed g W)) *ᵥ p'; refine Eq.trans ?_ ((forestDrag (S:=T m) (G:=G) p' hw).symm); exact congr_arg (fun L=> L*ᵥ p') (rise_roll (S:=T m) S ht.sign_f hp hS hb (ht.primary m))
    let I(i:ℕ):= packing (lower (M m)) (Z i); let y:= plead V (lower (M m)); let R:= shiftA (Catch.cap p) y; let f:= House.wind R (l+n+3) l; have he:GuardsL f (l+n+3-l):= (hF.attends (M m)).birth _ _ (by omega); have hh (i:ℕ) : Poem (I i):= poetic _ (coil_mirror _ hF.incarnate l i) _; have hh'(i:ℕ)(hi:i≤n) : ∀ t, jet f i t=design (I i) t:= by
       intro t; unfold f I Z; rw [House.wind_jet R l (l+n+3),if_pos (by omega),coil_pack,glitter]
    let L':= (∑ i∈stops n,slew i • (chart G).folded i (I i.length)); rw [sub_cols,parcel_sub]; rotate_left; · exact (hoist_price x hB hc hk hr).summ
    · exact (hoist_price x hN hY hk hm).summ
    erw [pack_hoist g hu x hu' hk hr, pack_hoist g hB x hc hk hr, pack_hoist g hN x hY hk hm, (show packing (lower (M m)) C'=L' from mountain_pack (fun i hi=>hl i hi.le) z (M m))]
    change design _ _ =_; simp_rw [hoist_read]; change design (I n) X'= design (I n) B' - design L' v; rw [hx, kin_stepL f he (by omega) I (fun i _=> hh i) hh', show bundleLink v=B' from link_nest (S:=T m) p']; apply congr_arg; unfold L' design; rw [verse_sum,map_sum]; simp only [verse_scale',map_smul]; rfl
end YM.Contacts.Procession.Hinges
