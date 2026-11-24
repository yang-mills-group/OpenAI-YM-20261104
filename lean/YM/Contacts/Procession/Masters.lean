import YM.Contacts.Procession.Lodge
/-!
# Reflection of gauge invariance through Wind, for packed roots only

Consumers get torus accounting.No assuming cover Schwinger expectations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Procession.Welcome
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Sun Xenon Kale Garf PertExtension.Series Radial Larch Ion Convoy
open scoped Classical Topology BigOperators NNReal Matrix ContDiff
variable {α β A:Type} [Fintype α]{T W:TableFee}{Γ:Gauge}{m n:Side}{x: Loc Γ 1}{k r p:ℕ}{σ:ℝ≥0}
open House
-- salve with single-root line
lemma lightens [Nonempty A] {l:Filter A}[l.NeBot]{F:House (Lines Γ m 1)}{P Q:A→House (Lines Γ m 1)} (ht:∀ i r v,Tendsto (fun a=> Q a i r v) l (𝓝 0)) (hp:∀ᶠ a in l,sealedL (P a) k)(he: ∀ a i,wind (P a) k i-wind F k i=wind (Q a) k i): sealedL F k:= by
   intro i hi; let f:= wind F k i; let p a:=wind (P a) k i; let q a:=wind (Q a) k i
   have hv {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] (Tq:E→ Link Γ m)(hT:AnalyticAt ℝ Tq 0)(x:E)(j:ℕ) : Tendsto (fun a=> jet (p a∘ Tq) j x) l (𝓝 (jet (f∘Tq) j x)) := by
      have hl:= viva (k:=k) l (α:=Loc Γ 1) i j x Tq hT Q (fun r i=> ht i r); have he a : jet (p a ∘ Tq) j x= jet (q a∘ Tq) j x+jet (f∘ Tq) j x:= by rw [show p a=q a+f from sub_eq_iff_eq_add.mp (he a i),show (q a+f) ∘ Tq=q a ∘ Tq+f∘Tq from rfl,serif (AnalyticAt.comp (g:=q a) (f:=Tq) (wind_ana ..) hT) (f ∘ Tq) (AnalyticAt.comp (g:=f) (f:=Tq) (wind_ana ..) hT)];
      simp_rw [he]; simpa using hl.add_const (jet (f∘Tq) j x)
   have hx (L: Link Γ m →L[ℝ] Link Γ m) (h:∀ᶠ a in l, p a ∘ (⇑L)=p a): f ∘ (⇑L)=f:= by
      let T:= L; refine instant (repeater (wind_controls ..) L) (wind_controls ..) (valued (k-i) (starts _ (wind_ana ..) _) (wind_ana ..) (fun x j hj=>?_)); exact tendsto_nhds_unique (hv _ (L.analyticAt _) x j) (show Tendsto _ _ _ from (hv _ analyticAt_id (x:Link Γ m) j).congr' (h.mono fun a ha=> by dsimp only; rw [ha]; rfl)) -- inference
   refine ⟨continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt),wind_ana ..,fun u=>congr_fun (hx (stain u) (hp.mono fun a ha=> funext ((ha i hi).color u))),?_⟩
   let P:=moveField (G:=Γ) (m:=m); let g:= (ContinuousLinearMap.snd ℝ (BaseSites Γ m) (Link Γ m)); have hl (f:Link Γ m→ℝ)(hf:AnalyticAt ℝ f 0): AnalyticAt ℝ (f∘ P) 0:=AnalyticAt.comp (by unfold P; rw [moveField_zero]; exact hf) moveField_analytic
   refine (show Rays (k-i) (f∘ P-f∘ g) from valued (k-i) (hl _ (wind_ana ..)) (starts _ (wind_ana ..) _) (fun x j hj=>?_)); exact tendsto_nhds_unique (hv _ moveField_analytic x j) ((hv _ (g.analyticAt _) x j).congr' (hp.mono fun a ha=> by have HE:= ha i hi; exact nightwalk (hl (p a) HE.analytic) (starts (p a) HE.analytic g) HE.grade j hj x|>.symm))
lemma packing_wind (H : House (Co n α))(h:m.val∣ n.val) (i x):wind (plead H (spool h)) k i x=wind H k i (still h x):= by
   unfold wind; refine sum_congr rfl fun j _=> ?_; unfold House.grate; split_ifs; · exact by unfold plead; rw [design_at,design_at,say_fold Summable.of_finite]; rfl
   rfl
lemma packing_guard (P:House (Lines Γ n 1))(h:m.val∣ n.val)(hp:sealedL P k): sealedL (plead P (spool h)) k:= by
   intro i hi; let Q:= wind (plead P (spool h)) k i; let U:=wind P k i; have hk (x): Q x=U (still h x):= packing_wind P h _ _; have hh:= hp i hi; refine ⟨continuous_iff_continuousAt.mpr (fun _=> (wind_ana ..).continuousAt), wind_ana ..,fun x v=>?_,?_⟩;
   · change Q _=Q v; rw [hk,hk,still_stain h]; apply hh.color
   let T:= U ∘ moveField; let A:Swatch Γ n→ℝ:= U ∘ Prod.snd; have hl: AnalyticAt ℝ A 0 := (hh.analytic).comp (f:= Prod.snd) contDiffAt_snd.analyticAt; have hu:AnalyticAt ℝ T 0 := AnalyticAt.comp (f:= moveField) (g:=U) (moveField_zero (G:=Γ) (m:=n)|>.symm ▸ hh.analytic) moveField_analytic
   change Rays _ (fun z:Swatch Γ m=> Q _-Q _); rw [show (fun z:Swatch Γ m=> Q (moveField z)-Q z.2)=(T-A) ∘ rise h Γ from funext fun z=> by rw [hk,hk,still_move h]; rfl]; exact merkin (hu.sub hl) hh.grade _ ((Convoy.rise h Γ).analyticAt _) (map_zero _)
lemma packing_sub (α β:Type)[Fintype α](H K:Field (Fin k) α)(f:α→β) : packing f (H-K)= packing f H-packing f K:= by funext i; simp [packing,cram,tsum_fintype,Finset.sum_sub_distrib]
lemma pledge_shift (p:ℕ)(H:House α)(X:α→β): plead (shiftA p H) X= shiftA p (plead H X):= by
   ext1 i; unfold shiftA; by_cases h:p ≤ i
   · rw [if_pos h]; ext1 k; change packing _ ((if p≤ i then _ else (0:Sun.St α)) k)= _; rw [if_pos h]
   rw [if_neg h]; ext1 k; change packing _ ((if p ≤ i then _ else (0:Sun.St α)) k)= _; rw [if_neg h]; ext i; simp [packing,cram]
def Spiral (m:Side)(k:ℕ): Side:= ⟨m.val*(k+1),by positivity⟩
lemma spiral_dvd (k:ℕ): m.val ∣ (Spiral m k).val:= dvd_mul_right ..
lemma spiral_h (m:Side): Tendsto (fun i=>(Spiral m i).val) atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> (show i ≤ (Spiral m i).val from le_trans (Nat.le_succ i) (Nat.le_mul_of_pos_left _ m.property))) tendsto_id
variable {Q:House (Node (Loc Γ 1))}{Y:∀ m:Side, House (Co m (Loc Γ 1))}
lemma Pact (h:Proper p Q)(hs:0<σ)(ht:∀ (m:Side) i j,Alive σ (W i j) (hush σ m*T i j) x (Q i j) m (Y m i j))(hn:∀ m:Side,∀ᶠ i:ℕ in atTop,Nation Γ (Spiral m i) p (Y (Spiral m i))): Nation Γ m p (plead Q (lower m)):= by
   refine ⟨properB p _ _ h,fun k=>?_⟩; let t:=p+2; let n:=k+3; let S:=shiftA t (plead Q (lower m)); let U(i:ℕ):=Spiral m i; let K(i:ℕ):= plead (Y (U i)) (spool (spiral_dvd (m:=m) i)); let B i:= shiftA t (K i); let R i:= B i-S; have he:Tendsto (fun j=>hush σ (U j)) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp (Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop (R:=ℝ)|>.comp (spiral_h m)).const_mul_atTop (NNReal.coe_pos.mpr hs)))
   have hV:∀ᶠ i:ℕ in atTop,sealedL (B i) n := (hn m).mono fun i h=> by rw [show B i= _ from (show _=plead (shiftA _ _) (spool (spiral_dvd i)) from (pledge_shift t _ _).symm)]; exact packing_guard _ _ (h.birth k)
   apply lightens (l:=atTop (α:=ℕ)) (Q:=R) ?_ hV (fun a i=> (wind_minus i i (k:=n) (B a) S).symm ) -- implicitly infer P? sp
   intro i r v; by_cases hp:t≤ i
   swap; · have hv a:R a i r=0:=by unfold R S B; simp [shiftA,hp]
           simp_rw [hv,Pi.zero_apply]; exact tendsto_const_nhds
   let H(j:ℕ):=ht (U j) (i-t) r; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun _=> by positivity) (fun j=> ?_) (g:=fun j=>hush σ (U j)*T (i-t) r) (by simpa using he.mul_const (T (i-t) r))
   let X:=Loc Γ 1; let p:Boys r (Co m X):= v; let ψ(j):=Y (U j) (i-t) r-packing (lower (U j)) (Q (i-t) r); let h:=spiral_dvd (m:=m) j; let u:=U j; let w:= packing (spool (α:=X) h) (ψ j);
   rw [show R j i r=w from ?_]; swap; · unfold w ψ; rw [packing_sub _ _,pack_twice _ (H j).room.summ,lowers_spool h]; unfold R B K S; simp only [Pi.sub_apply,shiftA,if_pos hp]
   let f(y:Boys r (Co u X)):=ψ j y; let e:= hinge (ι:=Fin r) (spool (α:=X) h); let V:Type:={y//e y=p}; change ‖∑' i:V,f i.val‖≤ _; have ht:=(H j).far.raw; refine (norm_tsum_le_tsum_norm ?_).trans (budget_crop (p:=fun y=>e y=p) ht|>.2.2); exact (budget_crop (p:=fun y=>e y=p) ht).2.1
end YM.Contacts.Procession.Welcome
