import YM.LocalTaylorR2.Exponent.Disc

/-!
 # Polynomial STILL invoice on every mask movement, even on full actual domain. Earn ReadyAll. Prefix and twisted peri label. Actual fields stipulated by Observatory
 -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Exponent
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n l p m:ℕ} {g v d A D x y β:ℝ} {χ:Chi}
open Reel PhysicalNext.Repeat Reel.Strand Candle Tender Mesh LocalTaylorR2.Price Charge RG01.Survive
-- reproduce Reel.corn for apparent read but all courses.Buoyant.
variable (H:Cash W s μ L Q o C T R)
variable {X:Molecule S} {b a t w D' θ ρ A' r e:ℝ}
variable (N:Captain H j b t v w A A' r D' e n χ)
include N
lemma stemVoy (V:Config G c)(q f:Port.Test T)(hq:Port.Burst H (H.unionP X) q)(hf:Port.Burst H (H.unionP X) f)(hv:Healthy (Pressure.temp s) (H.unionP X) V)(hz:(roster X).flags=∅) : memo V (episode H χ X (q+f))=memo V (episode H χ X q)+memo V (episode H χ X f):=by
   apply Filter.Germ.coe_eq.mpr; apply Reel.glassRight; refine March.trust (j:=j) N.position (fun U h ht=>?_)
   have hF i : Port.Burst H (H.unionP X) ((fun x:Bool=> if x then q else f) i):= by dsimp only; split <;> assumption
   have hy := Port.episodeSumBurst (K:=q+f) (p:=X) (fun a X u=> (show (q+f) a X u=∑ i:Bool,(if i then q else f) a X u from by simp)) N.oboe hz h (hq.plus hf) hF (ht.symm ▸ hv)
   filter_upwards [hy] with v hv; simpa only [Fintype.sum_bool,ite_true,ite_false,Bool.false_eq_true,Function.comp_apply] using hv
variable {V:Config G c} {ι:Type*} {w':ι → ℝ} {f':ι → Port.Test T}
lemma harvest' (V:Config G c)(hv:Healthy (Pressure.temp s) (H.unionP X) V) (h0:(roster X).flags=∅) (h:Filled (Pop' H (H.unionP X)) p w' f') : Filled ⊤ p w' (fun i=>memo V (episode H χ X (f' i))):= h.transfers (fun x=> memo V (episode H χ X x)) (fun _ _=> Submodule.mem_top) (fun x hx y hy=>stemVoy H N V _ _ hx hy hv h0) (fun a _ v=> by rw [show episode H χ X (v • a)= v • episode H χ X a from funext fun x=> Reel.scaleCast x a v]; exact memoScale ..)
variable (Φ : ι→Bevy T)(hΦ:∀ (i:LogIndex c f), Filled (Pop' H (H.supportP (identityLog i))) 1 w' (fun j=>Φ j i))
include hΦ
omit N in
lemma heirs (A:Support c) (h:H.unionP X⊆A)(q:Paint X k): Filled (Pop' H A) (inserts q) w' (fun j=> rafters (Φ j) q):=by
   let D:=Pop' H A; let K i j:= Φ j (i:↥(logs X)).val; let w i:= Series.rank (q i); let c' i:= ((w i).factorial:ℝ)⁻¹; let v i j:= c' i • (K i j^w i)
   have hh (i): Filled D (w i) w' (v i):= by
      have hp:H.supportP (identityLog i.val)⊆A:= (subset_biUnion_of_mem H.supportP ((log_occ ..).1 i.property)).trans h -- i confusion
      have hv:Filled D 1 w' (K i):= (hΦ i.val).transfers (fun x=>x) (fun _ h=> Port.Burst.mono h hp) (fun _ _ _ _=>rfl) (fun _ _ _=>rfl)
      have hk:= hv.power (w i) (Port.Burst.fixed 1) (fun _ hx _ hy=> Port.Burst.times hx hy) (popPow H); rw [one_mul] at hk; exact hk.scaling (c' i)
   rw [show (fun j=>rafters (Φ j) q)=∏ i,v i from ?_]
   swap
   · ext j F X w'; rw [Finset.prod_apply]; simp_rw [Finset.prod_apply]; apply prod_congr rfl; intro i _; change _/_=((w i).factorial:ℝ)⁻¹ * (K i j F X w')^w i; rw [div_eq_mul_inv]; exact mul_comm ..
   exact Filled.accumulate _ v w (fun i _=> hh i) (Port.Burst.fixed 1) (fun _ hx _ hy=>Port.Burst.times hx hy) (popPow H)

variable (U:H.ThinP){q: Orders k}
lemma atRod (V:Config G c)(hp:Healthy (Pressure.temp s) (H.smallAt U) V)(hx:q≠Candle.perch k): Filled ⊤ q.val w' (fun i=> memo V (Mesh.issue H (Φ i) χ U q)):=by
   unfold Mesh.issue; simp_rw [if_neg hx]
   by_cases he:live H U; swap
   · simp_rw [Mesh.ode,if_neg he]; exact Filled.steady _ Submodule.mem_top
   let A:= univ.filter fun i:Paint U.val k=> chooseSlot i=q; let X i (j:Paint U.val k):= episode H χ U.val (Mesh.warm H (Φ i) j); have hU i: ode H (Φ i) χ U q=∑ j∈A,X i j:= by ext x; rw [Mesh.ode,if_pos he,Finset.sum_apply]; rfl
   simp_rw [hU,map_sum]; convert! Filled.group (P:=⊤) (w:=w') (n:=q.val) A (fun i j=>memo V (X j i)) ?h using 1; swap
   · intro i hi; have ht :chooseSlot i=q:= (mem_filter.mp hi).2; have hv := harvest' H N V hp U.2.2 (heirs H Φ hΦ (H.smallAt U) (Subset.refl (H.unionP U.val)) i)
     unfold X; simp_rw [cups H _ i (ne_of_eq_of_ne ht hx)]; apply hv.onward
     have h : min (k+1) (inserts i)= q.val:=congr_arg Fin.val ht; have hZ: q.val ≠ k+1:=fun h=> hx (Fin.ext h); omega
   ext1 j; simp only [Finset.sum_apply]
end YM.LocalTaylorR2.Exponent
