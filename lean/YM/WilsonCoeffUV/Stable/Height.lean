import YM.WilsonCoeffUV.Stable.Uniform
/-!
# Sector payoff for continuation on normalized test argument & time cut

Height z_p slots independent from announced engineering d for unstable port.
Width inherited and period algebra orientation handled separately.
-/
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {P:Patch}{n c:Side}{V E:Type*}{r h D l j e k a m t u i:ℕ} {G:Gauge}{F:Labels.Frame G h}{s A X B C δ:ℝ}

section
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
variable {U: Gear G→Type*}(o: (I:Gear G)→ U I→Cover) (w: (I:Gear G)→ U I→ Site I.patch.L) (η y: (I:Gear G)→ U I→ℝ)
variable {T:(I:Gear G) → U I→ Rally (e+1) 0 I} (g:Meter (xpos e T) (dpos e T) η y) (f:∀ i,η i≤1)
variable (F P:(i:Gear G)→U i→ Pal V (YForest G))
include g f
lemma pool (p: Fallow (fun i x=> i.patch.L.val • o i x+lift (w i x)) u (xpos e T) (dpos e T) (fun i x=> η i x/i.patch.L.val) y (fun i x=> F i x m r) (fun i x=>P i x m r))
   : Fallow o u (xpos e T) (dpos e T) η y (fun i x=> slidesJ i.patch ((T i x).P.Q) (F i x) m r) (fun i x=> slidesJ i.patch ((T i x).Q.Q) (P i x) m r) :=by
   obtain ⟨n,H⟩:= p; refine ⟨n,fun i=>?_⟩; obtain ⟨a,h,q⟩:=H i
   have ht:= tender_nn (i.price.trans i.holds) (Helms i) u; have hp:=zero_le_one.trans i.bill_nn
   refine ⟨(r+1:ℕ)*((i.D*tender (Helms i) i.s u)^r* (9^u*a)),by positivity,fun x=>?_⟩
   let Y:= tiles i.patch.L (F i x m); let Z:= tiles i.patch.L (P i x m); let U:=η i x; have he:0≤ U:= g.charges i x; have hv:U≤1:= f i x
   simp only [slidesJ, Bank.prism]; convert! prism_purchase (P:=Y r) (Q:=Z r) (i.price.trans i.holds) (votes i (T i x)) (YieldP.travel he hv (q x)) he hv using 1; unfold Helms; ring
lemma slipping (p: ∀ m r,lowerGrade m r e k→ Fallow (fun i x=> i.patch.L.val • o i x+lift (w i x)) u (xpos e T) (dpos e T) (fun i x=> η i x/i.patch.L.val) y (fun i x=> F i x m r) (fun i x=>P i x m r))(h:m<e∨m=e∧k<r+2*j)
   : Fallow o u (xpos e T) (dpos e T) η y (fun i x=> let t:=(T i x).P; puck i.patch i.kernel i.angle t.R t.Q t.page (F i x) j m r) (fun i x=>let t:=(T i x).Q; puck i.patch i.kernel i.angle t.R t.Q t.page (P i x) j m r):= stadium o η y g f _ _ (fun _ _ he=> pool _ _ _ _ g f F P (p _ _ he)) r h
end

-- y = continuation fuel (zero possible), η varying at e,r stage. Parent origin 0.
structure SumT (I:Gear G)(e r D u:ℕ) where
   P : Rally (e+1) 0 I
   Y : Single G D
   Z : Single G D
   fund :ℝ
   η :ℝ
   large:0≤ fund
   clean:0≤η
   most:η≤1
   rent i j:lowerGrade i j e r → YieldP 0 (η/I.patch.L.val) u fund P.σ (Y i j) (Z i j)

variable {I:Gear G}
namespace SumT
abbrev x (T:SumT I e k D u):= T.P.x
abbrev σ (T: SumT I e k D u):= T.P.σ
end SumT
abbrev Hale (I:Gear G)(e r D u:ℕ):= SumT I e r D u× Site I.patch.L
abbrev team (G:Gauge)(e r D u:ℕ):=(fun (I:Gear G) (v:Hale I e r D u)=> v.1.P)
lemma hPeak (G:Gauge)(e k D u:ℕ): Meter (xpos e (team G e k D u)) (dpos e (team G e k D u)) (fun _ v=>v.1.η) (fun _ v=>v.1.fund):= ⟨fun _=>⟨fun v=>v.1.P.rich,fun v=>v.1.P.θ⟩,fun _ v=>v.1.clean,fun _ v=>v.1.large⟩

abbrev Drum (G:Gauge)(e r D u k:ℕ){V:(i:Gear G)→Type*} (F P:(i:Gear G)→ Hale i e r D u→ Ten (Vote D) (Cloth (V i)) k):= Fallow 0 u (xpos e (team G e r D u)) (dpos e (team G e r D u)) (fun _ v=> v.1.η) (fun _ v=> v.1.fund) F P
lemma inherit (p:lowerGrade m j e k)(D:ℕ)(u:ℕ): Fallow (fun (i:Gear G) x=> i.patch.L.val • (0:Cover)+lift x.2) u (xpos e (team G e k D u)) (dpos e (team G e k D u)) (fun i (x:Hale i e k D u)=> x.1.η/i.patch.L.val) (fun _ x=>x.1.fund) (fun i x=> gatherT i.patch x.2 (lift x.2) x.1.Y m j) (fun i x=> gatherT i.patch x.2 (lift x.2) x.1.Z m j):=by
    refine ⟨0,fun i=>⟨1,zero_le_one,fun v=>?_⟩⟩
    obtain ⟨x,w⟩:=v; let y:=lift w; let F:=soprano i.patch w D; let R:=gatherT i.patch w y x.Z; let T:=gatherT i.patch w y x.Y
    have ht:= x.rent m j p; have hu:=x.clean; let s:=x.η/i.patch.L.val
    have hx {Z:Single G D}{P:ℝ}(h: Fruit 0 s u (Z m j) P): Fruit y s u (F ∘ revolve y (Z m j)) P:=(((show Fruit y s u _ _ by simpa only [add_zero y] using h.turn y).touch F (by unfold s; positivity)).more (mul_le_of_le_one_left h.C (budgetS ..)))
    rw [pow_zero,one_mul,one_mul]; simp_rw [smul_zero,zero_add]; refine ⟨hx (Z:=x.Y) ht.wax,hx (Z:=x.Z) ht.wane,?_⟩
    have he: (F ∘ revolve y ((x.Y-x.Z) m j)) =T m j-R m j:= funext fun i=> map_sub F _ _; rw [show gatherT _ _ _ _ _ _ -_= _ from he.symm]; exact hx (Z:=x.Y-x.Z) ht.toll
lemma drum (h:m<e∨m=e∧k<r+2*j): Drum G e k D u r (fun I v=> awning I v.1.P.P v.1.Y v.2 j m r) (fun I v=>awning I v.1.P.Q v.1.Z v.2 j m r):= slipping (U:=fun i:Gear G=>Hale i e k D u) 0 (fun _ v=> v.2) (fun _ v=> v.1.η) (fun _ v=> v.1.fund) (hPeak G e k D u) (fun _ v=>v.1.most) _ _ (fun _ _ p=> inherit p D u) h
abbrev Trump (G:Gauge)(e k D u:ℕ):= (fun (I:Gear G) (v:SumT I e k D u)=> v.P)
abbrev Air (G:Gauge)(e k D u r:ℕ):=
  fun (X Y:(I:Gear G)→ SumT I e k D u→ ChamberTen G (Vote D) r)=>Fallow (fun _ _=>0) u (xpos e (Trump G e k D u)) (dpos e (Trump G e k D u)) (fun _ v=> v.η) (fun _ v=> v.fund) X Y
lemma Meter.air (G:Gauge)(e k D u:ℕ): Meter (xpos e (Trump G e k D u)) (dpos e (Trump G e k D u)) (fun _ v=>v.η) (fun _ v=> v.fund):= ⟨fun _=>⟨fun v=>v.P.rich,fun v=>v.P.θ⟩,fun _ v=> v.clean,fun _ v=> v.large⟩
lemma ingot {U V:(I:Gear G)→ Hale I e k D u→ ChamberTen G (Vote D) r} (p: Drum _ _ _ _ _ _ U V): Air G e k D u r (fun I t=> ∑ w:Site I.patch.L, U I (t,w)) (fun I t=>∑ w:Site I.patch.L,V I (t,w)):=by
    obtain ⟨d,H⟩:= p; refine ⟨d,fun i=>?_⟩; obtain ⟨A,h,f⟩:=H i; refine ⟨Fintype.card (Site i.patch.L)*A,by positivity,fun x=>?_⟩
    have he:= YieldP.sum (o:=0) (δ:=x.σ) (u:=u) (S:=Finset.univ) (A:=fun _=>A*x.x^d*x.fund) (P:=fun w=>U i (x,w)) (Q:=fun w=> V i (x,w)) (fun w _=> f (x,w)) x.clean
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←mul_assoc,←mul_assoc] at he; exact he
lemma Air.heroes (p:m<e∨m=e∧k≤r)(h:ℕ): Air G e k D u r (fun I v=> carnival I v.P.P h v.Y m r) (fun I v=>carnival I v.P.Q h v.Z m r):=by
   unfold carnival; apply Fallow.st (Bank.Slate.one (P:=fun i:Gear G=> tiara i.patch h) (Meter.air G e k D u).shine) _ (Meter.air G e k D u); apply ingot (U:=fun I v=>∑ j∈Finset.range (h+3*m), scoop (awning I v.1.P.P v.1.Y v.2 (j+1) m r)) (V:=fun I v=>∑ j∈Finset.range (h+3*m), scoop (awning I v.1.P.Q v.1.Z v.2 (j+1) m r)); exact Fallow.sum (fun j _=> Fallow.gleanS (drum (k:=k) (e:=e) (m:=m) (r:=r) (j:=j+1) (by omega))) (hPeak ..)
lemma echo_drum (p:lowerGrade m r e k)(h:ℕ): Air G e k D u r (fun I v=> hall I.patch h v.P.P.Q (v.Y m r)) (fun I v=> hall I.patch h v.P.Q.Q (v.Z m r)):=by
   unfold hall; apply Fallow.st (Bank.Slate.one (P:=fun i:Gear G=>tiara i.patch h) (Meter.air G e k D u).shine) _ (Meter.air G e k D u)
   have ht (I:Gear G)(w:Site I.patch.L)(t:Stand I)(Y:Single G D) : pulseS I.patch w t.Q (Y m r)= scoop (awning I t Y w 0 m r):= by unfold awning puck; rw [level]; unfold slidesJ pulseS; rw [inspectFace]; ext1 x; rw [scoop, Bank.prism,climb_cut,climb_cut]; rfl
   simp_rw [ht]; exact ingot (U:=fun I v=>scoop (awning I v.1.P.P v.1.Y v.2 0 m r)) (V:=fun I v=> scoop (awning I v.1.P.Q v.1.Z v.2 0 m r)) (Fallow.gleanS (drum (e:=e) (by unfold lowerGrade at p; omega)))
lemma stowed (p:lowerGrade m r e k)(h:ℕ): Air G e k D u r (fun I v=> helmet I v.P.P h v.Y m r) (fun I v=> helmet I v.P.Q h v.Z m r):=by
   simp_rw [tier_owns]; unfold lowerGrade at p; exact Fallow.plus (echo_drum (k:=k) p h) (Air.heroes (e:=e) (by omega) h) (Meter.air G e k D u)
lemma goldCoin (p:i≤ e)(a b:ℕ) : Bank.Slate (xpos e (Trump G e k D u)) (dpos e (Trump G e k D u)) (fun _ v=> coeff i (v.P.P.moving^a*(v.P.P.moving⁻¹)^b)) (fun _ v=>coeff i (v.P.Q.moving^a*(v.P.Q.moving⁻¹)^b)):=by
   obtain ⟨d,H⟩:=titles (G:=G) (i:=i) (e:=e+1) (by omega) 0 a b; refine ⟨d,fun I=>?_⟩; obtain ⟨A,h,f⟩:= H I; exact ⟨A,h,fun w=> f w.P⟩
lemma Air.resin42 (p:m≤e)(h:ℕ): Air G e k D u r (fun I v=> veering I v.P.P h v.Y m r) (fun I v=> veering I v.P.Q h v.Z m r):=by
   unfold veering; apply Fallow.sum _ (Meter.air G e k D u); intro i hi; have hv:=Finset.mem_range.mp hi; exact Fallow.st (goldCoin (e:=e) (i:=m-i) (by omega) i r) (stowed (k:=k) (e:=e) (show lowerGrade i r e k from Or.inl (hv.trans_le p)) h) (Meter.air ..)
lemma Air.paintH (h:ℕ): Air G e r D u r (fun I v=> carnival I v.P.P h v.Y e r+veering I v.P.P h v.Y e r) (fun I v=> carnival I v.P.Q h v.Z e r+veering I v.P.Q h v.Z e r):= Fallow.plus (Air.heroes (k:=r) (e:=e) (G:=G) (show e<e ∨ e=e∧r≤r from Or.inr ⟨rfl,le_rfl⟩) h) (Air.resin42 (k:=r) (e:=e) (m:=e) le_rfl h) (Meter.air ..)
lemma Air.higher (p:lowerGrade m j e k)(h:ℕ): Air G e k D u j (fun I v=> fanfare I v.P.P h v.Y m j) (fun I v=>fanfare I v.P.Q h v.Z m j):=by
    unfold fanfare Blue.mix; apply Fallow.sum _ (Meter.air ..); intro i hi; have hv:=Finset.mem_range.mp hi; unfold lowerGrade at p; exact Fallow.st (goldCoin (e:=e) (i:=m-i) (by omega) i j) (stowed (e:=e) (k:=k) (show lowerGrade i j e k from by unfold lowerGrade; omega) h) (Meter.air ..)
end YM.WilsonCoeffUV.Shard
