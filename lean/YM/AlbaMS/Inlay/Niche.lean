import YM.AlbaMS.Inlay.Wave

/-!
# Base and shifted gauge units

Also transport exact change between lenses applied BEFORE computing effective
recurrences. Blank convention top horizon. (No assertion about existence of Tune choices with limits.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Tune
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil Net
variable {V W I J R S : Type*}{G:Gauge}[CommRing R][CommRing S]
variable (P:Tune R){T:Tune S}
variable {Ω:Net V I}{H:Net W J}{a:ℝ}{b:Bool}{F O:Heave G V I ℝ} {Y:Heave G V I R}{k :ℕ}{α:Flit G V}{β:Flit G I}
lemma up_add (Ω Q:Heave G V I ℝ): P.up k (Ω+Q)=P.up k Ω+P.up k Q:=by unfold up; simp_rw [map_add]
lemma up_smul (r:ℝ): P.up k (r • F)= P.D r • (P.up k F):=by unfold up; rw [Wind_smul]; simp only [map_smul]
lemma excited (h: Tone b F): Tone b (P.up k F):= ((h.seep _ _ _).loom (n:=k) P.z).weft _ -- argument
lemma bounded (h:IsNilpotent P.z): FinRank (P.up k F):= by obtain ⟨j,hj⟩:= h; exact ⟨_, (loom_power P.z j hj k).weft P.loomT⟩
structure Overlay (P:Tune R)(T:Tune S)(K:R→+* S) : Prop where
  a : T.a=P.a
  z : T.z=K P.z
  A : (T.A:S)= K (P.A:R)
  Gc : (T.Gc:S)= K (P.Gc:R)
  D : ∀ r,T.D r=K (P.D r)
namespace Overlay
variable {P}{K:R→+* S}
private lemma covers (W:Rˣ)(U:Sˣ)(h:(U:S)=K (W:R)): ((U⁻¹:Sˣ): S)=K ↑(W⁻¹):=by
  refine IsUnit.mul_left_cancel U.isUnit ?_; rw [Units.mul_inv,h,← map_mul,Units.mul_inv,K.map_one]
lemma roll (h:Overlay P T K)(i:Leaf G V I): T.loomT i= K (P.loomT i):= by rcases i with (i|i)|(i|i) <;> unfold loomT <;> dsimp only [Sum.elim_inl, Sum.elim_inr] <;> first|(rw [h.a,h.D,map_mul, covers _ _ h.A,map_pow])|(rw [h.a,h.D,map_mul,h.A])|(rw [h.a,h.D,map_mul,covers _ _ h.Gc,map_pow])|(rw [h.a,h.D,map_mul,h.Gc])
lemma lay (h:Overlay P T K): Wind _ K (P.up k F) = T.up k F:= by
  ext l; simp_rw [up,blows,seep_read,wefts,looms,seep_read];
  change K (_* (_* (P.D (F l))))=_*(_* T.D (F l)); have hv : K (List.map P.loomT l).prod= (List.map T.loomT l).prod:=by
    induction l with|nil=>exact K.map_one| cons i l ih=> simp only [List.map_cons,List.prod_cons,h.roll i,map_mul,ih]
  rw [map_mul,hv,map_mul,map_pow,← h.z,h.D]
lemma fire (h:Overlay P T K): Wind _ K (P.fuelT F O)=T.fuelT F O:= by unfold fuelT;rw [map_sub,h.lay,h.lay]
end Overlay
lemma Wind_id : Wind (@ø (Flit G V) (Flit G I)) (RingHom.id R) Y= Y:=rfl
lemma fuel_base (ha:0<a)(h:needy 2 F)(he:needy 1 O): (baseT a ha).fuelT F O= kinetic a ha F:=by
  unfold fuelT up; simp_rw [baseT,Wind_id,loom_zero h, loom_zero (needy.founder O), he.ranklow Nat.zero_lt_one,map_zero,sub_zero]; rfl
lemma kin_work (ha:0<a) : kinetic a ha F=(baseT a ha).up 2 (rankn 2 F):=by
  let P:=baseT a ha; change _=P.up _ _
  unfold kinetic up; have hp:= rankn.heg F 2; rw [show P.z=0 from rfl, show (Wind _ P.D) (rankn 2 F)=rankn 2 F from Wind_id, loom_prec 0 2 hp]; rw [Nat.sub_self,pow_zero,one_smul]
variable [Fintype V] [Fintype I]
lemma kinetic_cross (u:Receipt G Ω H)(ha:0<a) : u.track (kinetic a ha F)=kinetic a ha (u.track F):=by
  let P:=baseT a ha

  rw [kin_work,kin_work, ← show u.track (rankn 2 F)=rankn 2 (u.track F) from shot_rank 2]; exact P.commute u 2 _
omit [Fintype V] [Fintype I] in
lemma rank5 {C:Heave G V I R}(h:Heg 2 C): Heg 2 (weft P.loomT C):=fun l hl=>h l fun hu=>hl (by simp [wefts,hu])
omit [Fintype V] [Fintype I] in
lemma two_k (ha:0<a): Heg 2 (kinetic a ha F):= rank5 (baseT a ha) (rankn.heg F 2)
omit [Fintype V] [Fintype I] in
private lemma hits (i:Leaf G V I) : weft P.loomT (varC R ø i)= P.loomT i • varC R ø i:= by
  ext l; by_cases h:l=[i]<;>simp [wefts,var_read,h]
lemma factors (c:G.Color) : weft P.loomT (Wind _ P.D (hill (V:=V) (I:=I) c))= P.D (P.a^3) • Wind _ P.D (hill (V:=V) (I:=I) c):=by
  have he (i:Leaf G V I): Wind _ P.D (varC ℝ ø i)=varC R ø i:=by ext l; by_cases h:l=[i] <;> simp [blows,seep_read,var_read,h]
  have hh (U:Rˣ) : P.D P.a ^ 2 * (↑(U⁻¹):R)*(P.D P.a*U)=P.D (P.a^3):=by
    rw [mul_assoc,_root_.mul_left_comm (↑(U⁻¹):R) (P.D P.a), Units.inv_mul,mul_one, map_pow, ← pow_succ]
  have ht (x y:Flit G V) : weft P.loomT (K (B:=Flit G I) R x*Loft.A R y)= P.D (P.a^3) • (K R x*Loft.A R y):=by rw [weft_mul,P.hits _,P.hits _, smul_mul_assoc,mul_smul_comm,smul_smul]; exact congr_arg (· • _) (hh P.A)
  have hv (x y:Flit G I): weft P.loomT (L (E:=Flit G V) R x*C R y)= P.D (P.a^3) • (L R x*C R y):=by rw [weft_mul,P.hits _,P.hits _, smul_mul_assoc,mul_smul_comm,smul_smul]; exact congr_arg (· • _) (hh P.Gc)
  unfold hill; simp_rw [Finset.mul_sum,mul_smul_comm,map_add,map_sum,Wind_smul,map_smul,map_mul]; simp_rw [K, Loft.A,C,L,he]; unfold Loft.A K at ht; unfold L C at hv; simp_rw [ht,hv]; simp_rw [smul_add,Finset.smul_sum,smul_comm (P.D (P.a^3))] -- may loop
lemma shiftT (c:G.Color)(H:Runs Ω)(Q:Grove (ink G V))(h:∀ i, DC i O=0):
    air (fun i=>P.D (fill c i)) (P.fuelT (superb (grit G I) Ω.chat (bare Q)) O)=(P.D (P.a^4) * P.coul) • (Wind ø P.D (hill c)):=by
  have he : air (fill c) O=0:= air_simple (fill c) O h
  unfold fuelT up; rw [map_sub];
  let v:=P.D P.a*P.Gc; have hv (i:Flit G I): P.loomT (Place.c (E:=Flit G V) i)=v:=rfl
  simp_rw [air_rig _ _ v _ hv]
  have hb (w:Heave G V I R) : air (fun i=>P.D (fill c i)) (weft (fun _=>P.z) w)=P.z • weft (fun _=>P.z) (air (fun i=>P.D (fill c i)) w):= Net.air_rig _ _ _ _ (fun _=>rfl)
  rw [air_step (k:=1), ← air_move, Ω.shift_force c H, wefat, hb, ← air_move,he]; have hc:Heg 2 (Wind ø P.D (hill (V:=V) (I:=I) c)) := (Net.height (V:=V) (I:=I) c).seep _ _;
  rw [loom_prec P.z 1 hc,show 2-1=1 from rfl, pow_one,map_smul,P.factors]; simp only [map_zero,smul_zero,sub_zero,smul_smul]; congr 1; unfold v Tune.coul; rw [map_pow,map_pow]; ring
end YM.MSBar.Inlay.Tune
