import YM.RegulatorIR.Capture.Ports

/-!
# Older scalar stability

No inserted convergence input except through tested-stock & geometric R envelope. Used
AFTER taking UV limit in comparison with genuinely unconditioned diagrams. Not
asserting cover precision ellipt etc constructed. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Older
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Profiles Sources Centered Capture
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I U: Type}{q u b p a i j e k d m r s:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{C D J K:Choice M}
variable {S:Heir n G} (R: Reel S)(T:S.Accounts)(Z:(portraitR T).Report m)
variable {Γ:Flap M→ Layer (Foot G) (Foot G)} {V: Flap M→ Bride G} {c:Flap M→ℝ≥0∞}{γ:ℝ}

-- exact tiling old l4 divide. Work for jumps.
lemma broadly {l:ℝ}{g:Room→ℝ}(h:Centered.Rhythm l g)(_hl:0<l)(f:Side) : Centered.Rhythm (l*f.val) g:=fun y x=> by rw [← turns_site]; exact h _ x -- l free bind
lemma titled {l:ℝ}{g:Room→ℝ}(h:Centered.Rhythm l g)(hl:0<l)(f:Side)(hp:Odd f.val)(hh:IntegrableOn g (seatX (l*f.val))) : weighT (l*f.val) g=weighT l g:=by
 rw [meanTiles f hl hp hh]; simp_rw [show ∀ i:Site f, (fun x=>g (location f l i+x))=g from fun i=>funext (h _)]; rw [sum_const,card_univ,Lattice.site_card]; simp [tally,display]

include R in
lemma scale_copy {g:W→Room→ℝ}(h:∀ w,Centered.Rhythm (S.l (J.choose w)) (g w))(hi:∀ w:W,∀ l:ℝ,0<l→IntegrableOn (g w) (seatX l))(hv:J.age ≤ K.age): ∀ w,weighT (S.l (J.choose w)) (g w)=weighT (S.l (K.choose w)) (g w):= by
 intro w
 have H:∀ x:Page J.after.spans, let i:= J.after.page x; Centered.Rhythm (S.l i) (g x.bindW) ∧ weighT (S.l i) (g x.bindW)= weighT (S.l (J.choose x.bindW)) (g x.bindW):=by
    refine Page.proves (fun w=>⟨h w,rfl⟩) ?_
    intro w ih i; let y:=(J.after.wing w); let t:=(R.steps y).patch.L
    have he:= S.hl y.prev; have hl:0<S.l y.prev*t.val:= by positivity
    rw [show S.l i=S.l y.prev*t.val from scaledCard R y]; exact ⟨broadly (h:=ih.1) he t,(titled ih.1 he t (R.steps y).patch.odd_side (hi w.volW _ hl)).trans ih.2⟩
 let x:= birth J K w
 rw [← Capture.rebirth _ _ hv w]; exact (H x).2.symm

variable (H:Seated S T Z R.feeMarg L u b q p a 1 γ c D)
include H
lemma joining_price (hv:D.age ≤ J.age)(h:J.age≤ K.age)(he:e ≤ p) : ∃ c: ℝ, ∃ d:ℕ,0 ≤ c ∧ ∀ w x,
 ‖medium S T Z K e w x-medium S T Z J e w x‖ ≤ c*(L.val w).toReal^d*(S.l (J.choose w)^γ)⁻¹:=by
 let f:= film W; let T':= motif S; let g:= glow f H.light; let Q:= galaxy f H.space; let k:= spool D f; let t:= spool J f
 let U:= T'.warmer g; have hq:= T'.appear _ Z g H.many H.consent H.sanctity (fun _=> ENNReal.one_ne_top)
 let l':= S.softnessWeight γ; let l:= T'.softnessWeight γ
 have hx:k.age ≤ t.age:= fun w=> hv (f w)
 have hh:T'.Bend _ Z (u+b+b) p t (dwell W) l 1 1 (L.us (film W)):= { hq with young:=fun i he j hp=>T'.success _ _ Q.prim Q.space U hq (by omega) hx he hp }
 have hz:= T'.woven _ _ Q.prim Q.space U hh (by omega) (j:=spool K f) (fun w=> h (f w)) he
 let v(w:plane W):= S.l (J.choose w.1)
 have hV (w):ticket l 1 (t.choose w)= ENNReal.ofReal ((v w^γ)⁻¹):=by rw [ticket,Pi.one_apply,one_mul, ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (S.hl _) _)];rfl
 let x(w:plane W):=(v w^γ)⁻¹
 have hb : Carry (L.us f) (fun w=> ENNReal.ofReal (x w)) fun w=> ‖medium S T Z K e w.1 w.2-medium S T Z J e w.1 w.2‖ₑ:=by
    convert hz using 1
    · ext1 w;exact (hV w).symm
    rfl
 obtain ⟨a,k',ha,H⟩:= Centered.Carry_rt (fun w=>show 0≤x w from inv_nonneg.mpr (Real.rpow_pos_of_pos (S.hl _) _).le) hb
 exact ⟨a,k',ha,fun w x=> H (w,x)⟩
-- need q=6 for Malm
lemma later_j (hq:q=6)(hv:D.age≤ J.age)(h:J.age ≤ K.age) (he:e≤p) (hΓ:Leading Z) (ht:∀ w, Centered.Rhythm (S.l (J.choose w)) (medium S T Z J e w)) : ∃ c:ℝ,∃ d:ℕ,0≤c∧∀ w,
 ‖diffuse S T Z K e w-diffuse S T Z J e w‖≤ c*(L.val w).toReal^d*(S.l (J.choose w)^γ)⁻¹:=by
 subst q
 obtain ⟨c,k,hc,Hc⟩:=joining_price R T Z H hv h he
 have hp (w:W)(t)(l:ℝ)(hl:0<l): IntegrableOn (medium S T Z J e w) (cube t l):= medium_int Z hΓ H he hv w t l hl.le
 have hy:= scale_copy R ht (fun w l hl=>hp w _ _ hl) h
 refine ⟨c,k,hc, fun w=> ?_⟩
 let v:= S.l (K.choose w);have hh:0<v:= S.hl _
 change ‖weighT v _ - weighT (S.l (J.choose w)) (medium S T Z J e w)‖ ≤ _
 rw [hy]; unfold weighT; rw [minusW (medium_int Z hΓ H he (le_trans hv h) w _ _ hh.le) (hp w _ v hh)]; exact worth hh (fun x _=> Hc w x)
end YM.RegulatorIR.Older
