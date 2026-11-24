import YM.WilsonCoeffUV.Root.Post.Fabric
/-!
# Registration of budgets: unconditional clustered tariff of strict part, linear in normalized amplitude unknown +.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{U V E:Type*}{r h D l j e k a m t:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X B C δ:ℝ}
variable {I:Bulb G}{i:ℕ}

abbrev Tern (G:Gauge)(e r D:ℕ):= fun I:Bulb G=> Tand.x (I:=I) (e:=e) (r:=r) (D:=D)
abbrev Scorn (G:Gauge)(e r D:ℕ):= fun I: Bulb G=> Tand.σ (I:=I) (e:=e) (r:=r) (D:=D)
lemma Fabric.grove {U V:(I:Bulb G)→ Etch I e r D→ ChamberTen G (Vote D) k}(u:Fabric (ink e r D) (dye e r D) Bulb.exitS U V):
   Fabric (Tern G e r D) (Scorn G e r D) Bulb.exitS (fun I v=>∑ w:Site I.path.patch.L, U I (v,w)) (fun I v=> ∑ w:Site I.path.patch.L,V I (v,w)):=by
   obtain ⟨d,H⟩:=u; refine ⟨d,fun I=>?_⟩; obtain ⟨C,h,e'⟩:= H I
   refine ⟨(I.path.patch.L.val:ℝ)^4*C,by positivity,fun i=>?_⟩; have he := Shelf.sum (A:=fun w:Site I.path.patch.L=> C*i.x ^d) (s:=I.exitS) (δ:=i.σ) (Q:=fun w=>V I (i,w)) (S:=Finset.univ) (fun w _=> e' (i,w));
   rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,tier_out,← mul_assoc] at he; exact he
lemma Fabric.postCrown (h:ℕ)(p:m<e∨m=e∧k≤ r)(D): Fabric (Tern G e k D) (Scorn G e k D) Bulb.exitS (fun I v=> carnival I.path v.P.P h v.Y m r) (fun I v=> carnival I.path v.P.Q h v.Z m r):=by
   unfold carnival; apply Fabric.mag (Bank.Slate.one (P:=fun I:Bulb G=> tiara I.path.patch h) (matur e k D)); apply Fabric.grove (U:=fun I v=> ∑ i∈Finset.range (h+3*m), scoop (ent _ _ _ (i+1) m I v r)) (V:=fun I v=>∑ i∈Finset.range (h+3*m), scoop (exitC _ _ _ (i+1) m I v r)); apply Fabric.sum (welling e k D); intro i _
   exact (centuries e k D m (i+1) r (by omega) _ (fun i:Bulb G=> i.positive.le) Bulb.vio).scoopV
lemma Fabric.padHall (h:ℕ)(p:lowerGrade m r e k)(D): Fabric (Tern G e k D) (Scorn G e k D) Bulb.exitS (fun I v=> hall I.path.patch h v.P.P.Q (v.Y m r)) (fun I v=> hall I.path.patch h v.P.Q.Q (v.Z m r)):=by
   unfold hall; apply Fabric.mag (Bank.Slate.one (P:=fun I:Bulb G=> tiara I.path.patch h) (matur e k D));
   let f I (v:Etch I e k D):=pulseS (G:=G) I.path.patch v.2 v.1.P.P.Q (v.1.Y m r); let g I (v:Etch I e k D):=pulseS (G:=G) I.path.patch v.2 v.1.P.Q.Q (v.1.Z m r)
   apply Fabric.grove (U:=f) (V:=g); refine ⟨1,fun I=>?_⟩
   let W:= tiePay (Pick I.path) r (I.s-I.exitS); have he :0≤ W:=tie_nn (sub_pos.mpr I.vio) _; have hY:=zero_le_one.trans I.path.bill_nn
   refine ⟨(r+1:ℕ)*I.path.D^r*Real.exp (8*I.s)*W,by positivity,fun ⟨x,w⟩=>?_⟩
   let L:= I.path.patch.L; let U:=gatherT I.path.patch w (lift w) x.Y; let V:=gatherT I.path.patch w (lift w) x.Z
   have hv:= Shelf.prismLens (P:=tiles L (U m)) (Q:=tiles L (V m)) ((pays_feather _ w (x.rent m r p)).portal I.ports (I.positive.trans I.vio).le) (x.P.Υ.mono (I.outlet.trans I.path.holds.le)) I.vio I.positive.le
   unfold f g pulseS; simp_rw [inspectFace];
   rw [pow_one,mul_right_comm _ W, mul_assoc (((r+1:ℕ):ℝ)*I.path.D^r),mul_comm (Real.exp _)]; exact hv
lemma Fabric.stoked (h:ℕ)(p:lowerGrade m r e k)(D): Fabric (Tern G e k D) (Scorn G e k D) Bulb.exitS (fun I v=> helmet I.path v.P.P h v.Y m r) (fun I v=>helmet I.path v.P.Q h v.Z m r):=by
   simp_rw [tier_owns]; unfold lowerGrade at p; exact (Fabric.padHall (G:=G) h p D).add (Fabric.postCrown h (show m<e∨m=e∧k≤ r by omega) D) (matur e k D)
lemma glareC {g:ℕ}(hi:g ≤ e)(r a b D): Bank.Slate (Tern G e r D) (Scorn G e r D) (fun _ v=> coeff g (v.P.P.moving^a*(v.P.P.moving⁻¹)^b)) (fun _ v=>coeff g (v.P.Q.moving^a*(v.P.Q.moving⁻¹)^b)):=by
   obtain ⟨d,H⟩:= titles (G:=G) (i:=g) (e:=e+1) (by omega) 0 a b; refine ⟨d,fun I=>?_⟩; obtain ⟨A,h,v⟩:= H I.path; exact ⟨A,h,fun i=>v i.P⟩
lemma Fabric.slide42 (e r l m D h:ℕ)(v:l≤e): Fabric (Tern G e r D) (Scorn G e r D) Bulb.exitS (fun I v=> veering I.path v.P.P h v.Y l m) (fun I v=> veering I.path v.P.Q h v.Z l m):=by
   unfold veering; apply Fabric.sum (matur e r D); intro i hi; have hh:= Finset.mem_range.mp hi; exact Fabric.mag (glareC (e:=e) (g:=l-i) (by omega) r i m D) (Fabric.stoked h (show lowerGrade i m e r from Or.inl (lt_of_lt_of_le hh v)) D)
lemma Fabric.resinH (e r h D:ℕ): Fabric (Tern G e r D) (Scorn G e r D) Bulb.exitS (fun I v=> carnival I.path v.P.P h v.Y e r+veering I.path v.P.P h v.Y e r) (fun I v=>carnival I.path v.P.Q h v.Z e r+veering I.path v.P.Q h v.Z e r) := (Fabric.postCrown (G:=G) h (m:=e) (k:=r) (Or.inr ⟨rfl,le_refl r⟩) D).add (Fabric.slide42 e r e r D h le_rfl) (matur e r D)
lemma Fabric.higher (p:lowerGrade i j e k)(h D): Fabric (Tern G e k D) (Scorn G e k D) Bulb.exitS (fun I v=> fanfare I.path v.P.P h v.Y i j) (fun I v=> fanfare I.path v.P.Q h v.Z i j):=by
    unfold fanfare Blue.mix; apply Fabric.sum (matur e k D); intro a ha; have hv:=Finset.mem_range.mp ha; unfold lowerGrade at p; refine Fabric.mag (glareC (e:=e) (g:=i-a) (by omega) k a j D) (Fabric.stoked h ?_ D)
    unfold lowerGrade; omega
end YM.WilsonCoeffUV.Cosmos
