import YM.SchemeConversionRG11.FirstW.Fade.FirstBreath
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology
open scoped Topology BigOperators Classical
variable {T:Itinerary}{V E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup V][NormedSpace ℝ V]{G:Gauge}
variable {A B C: Sight T G} {f g:Hall T E}{p:Hall T F}{R r:ℝ}
def Dawn (T:Itinerary) (R:ℝ)(f: Hall T E): Prop:=∀ r:ℝ,0<r → r<R → ∀ p : Hall T (E→L[ℝ] ℝ), Placed T r p → Pleased T (Town R) p → Helen (tollH T f p)
lemma Dawn.up (h:Dusk T f): Dawn T R f:=fun r hr he p H ⟨_,Y⟩=> h r _ hr he p H _ Y
lemma Dawn.add (h:Dawn T R f)(e:Dawn T R g): Dawn T R (f+g) := by
 intro r hr he p H Y; obtain ⟨x,h⟩:= h r hr he p H Y; obtain ⟨v,hp⟩:=e r hr he p H Y; exact ⟨x+v, (h.add hp).congr (fun i=> by simp only [tollH,Pi.add_apply,map_add,Finset.sum_add_distrib,mul_add])⟩
lemma Dawn.scale (h:Dawn T R f)(c:ℝ): Dawn T R (c • f):=by
 intro r hr he p H Y; obtain ⟨x,h⟩:= h r hr he p H Y; refine ⟨_,(h.const_mul c).congr fun i=>?_⟩; simp only [tollH,Pi.smul_apply,map_smul,smul_eq_mul,←Finset.mul_sum]; ring
lemma Dawn.uses (h:Dawn T R f)(e:Pleased T (Town R) p)(B:E→L[ℝ] F→L[ℝ] V): Dawn T R (fun i x=> B (f i x) (p i x)) := by
 let L: (V→L[ℝ] ℝ) →L[ℝ] (E→L[ℝ] V) →L[ℝ] (E→L[ℝ] ℝ):= ContinuousLinearMap.compL ..
 let Y:=B.flip
 intro r hr he q H hp; obtain ⟨D,Dh⟩:=e
 apply h r hr he (fun i x=>L (q i x) (Y (p i x))) (Eventually.mono H (fun i hi x hx=> hi x (fun h=>hx (by simp only [h,map_zero, zero_apply])))) (Pleased.map₂ hp (show Pleased T (Town R) (fun i x=> Y (p i x)) from ⟨_,Dh.map _⟩) L)
lemma Dawn.mail (h:Dawn T R f)(s:Cover): Dawn T R (mailR T f s):= by
 intro r hr hp p H h; -- collision
 obtain ⟨q,hq,hR⟩:=exists_between hp
 obtain ⟨v,B⟩:= (‹Dawn T R f› q (lt_trans hr hq) hR (mailR T p (-s)) (H.flow hq _) (h.by _))
 refine ⟨v,B.congr fun i=>?_⟩; unfold tollH mailR; simp_rw [map_neg]; rw [penR]
lemma swayD (h:CalmS T A)(e:HatP T (Town R) B)(a:Walk): Dawn T R (fun i x=> swerve x a (A i) (B i)) ∧ Dawn T R (fun i x=>swerve x a (B i) (A i)):= by
 induction a with
 | nil=> simp only [swerve,LinearMap.zero_apply]; exact ⟨Dawn.up dusk_zero,Dawn.up dusk_zero⟩
 | cons i w ih=>
   have H₁:=ih.1.mail i.vec; have H₂:=ih.2.mail i.vec; rw [mail_vec] at H₁ H₂; have hb:= (rushP h w).mail i.vec; have he:= (walkP e w).by i.vec; rw [mail_vec] at hb he
   obtain ⟨L,H⟩:= doubles G.ad; simp only [swerve_eq,←H]; have hv: Dusk T (peakC T A i):= by rw [lookC]; exact ((h _).mail _).scale _
   exact ⟨((Dawn.up hv).uses he L|>.add H₁), ((Dawn.up hb).uses (e.leg _) L.flip |>.add H₂)⟩ -- flip defeq
lemma spireD (h:CalmS T A)(e:HatP T (Town R) B)(a:Walk): Dawn T R (fun i x=>spire G x a (A i) (B i)):= by
 simp only [spire,LinearMap.smul_apply,LinearMap.add_apply, LinearMap.flip_apply]; exact Dawn.scale ((swayD h e a).1.add (swayD h e a).2) _
def SeatD (T:Itinerary)(A B C: Sight T G)(i j:Step): Hall T ℝ:= fun s x=> (T.gap s)⁻¹ * tower G x (icon i j) (A s) (B s) (C s)
def Dra (T:Itinerary)(A B C:Sight T G)(i j:Step): Hall T ℝ:=fun s x=> inner ℝ (rushC T A i j s x) (spire G x (icon i j) (B s) (C s))
lemma rateD (A B C:Sight T G)(i j:Step): SeatD T A B C i j=(-1/48:ℝ) • (Dra T A B C i j + Dra T B C A i j + Dra T C A B i j) := funext fun s=>funext fun x=>by simp only [SeatD,Dra,rushC,tower_eq, Pi.smul_apply,Pi.add_apply, real_inner_smul_left, smul_eq_mul]; ring
lemma loadD (T:Itinerary) (U V W:Sight T G)(i j:Step)(k:ℕ)(x:Site (T.period k)): tower G x (icon i j) (T.gap k • U k) (T.gap k • V k) (T.gap k • W k)= T.gap k ^ 4 * SeatD T U V W i j k x:= by
 simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,SeatD]; field_simp [(T.positive k).ne']
lemma SeatD.Pays (h:CalmS T A)(e:HatP T (Town R) B) (p:HatP T (Town R) C)(i j:Step): Dawn T R (SeatD T A B C i j):= by
 rw [rateD]; apply Dawn.scale; have he:Dawn T R (Dra T A B C i j):= (Dawn.up (rushD h i j)).uses (spireP e p _) (innerSL ℝ)
 have hv : Dawn T R (Dra T C A B i j):=(spireD h e _).uses (seesP p i j) (innerSL ℝ).flip
 have hq : Dawn T R (Dra T B C A i j):= by unfold Dra; simp_rw [spire_comm (A:=C _)]; exact (spireD h p _).uses (seesP e i j) (innerSL ℝ).flip
 exact (he.add hq).add hv
lemma tollD (h:CalmS T A)(e: HatP T (Town R) B)(p:HatP T (Town R) C)(i j:Step) (Q:Hall T ℝ)(u:Pleased T (Town R) Q)(hr:Placed T r Q)(hp:0<r)(he:r<R): Helen (fun s=> T.gap s ^ 4 * ∑ x, Q s x* SeatD T A B C i j s x) := by
 let L:= ContinuousLinearMap.mul ℝ ℝ; obtain ⟨Y,u⟩:=u
 exact SeatD.Pays h e p i j r hp he (fun s x=> L (Q s x)) (Eventually.mono hr (fun i hi x hx=> hi x (fun h=>hx (show L (Q i x)=0 from h ▸ map_zero _)))) (show Pleased .. from ⟨_,u.map L⟩)
end YM.RG11.FirstW
