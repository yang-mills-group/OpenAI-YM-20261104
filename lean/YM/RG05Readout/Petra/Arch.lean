import YM.RG05Readout.Petra.Basalt
/-!
# Dummy root at grouping

Grow Bud **after** passage, preserving polynomial expenditures at crest and
forces.No fake disjointness for the dummy; the real n step requires literal b
focus to be its announced output call at *every* tested center, not simply allow
one nearby. This will give actual Blade at precisely that root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Petra
open Function Filter Lattice Wilson RG Source Extra.Histories Push Local
open Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station
open Ribbons Ribbons.Fibers Ribbons.ManyCopies Many
open MeasureTheory Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {k m p N d b i c:ℕ}{V W:Type}[DecidableEq V][Fintype V]
set_option quotPrecheck false
-- abbreviation ambiguity Address.Bud
local notation "B"=>MergeProof.Ribbon.Bud V
local notation "O"=>Option V
local notation "Z"=>MergeProof.Ribbon.Bud (Option V)
variable {n:Side}
namespace Root
abbrev hole : Many.License (MergeProof.Ribbon.Bud (Option V)) (MergeProof.Ribbon.Bud V) some:= fun _ _=> mem_univ _
-- impl.repr heft.Ne add root all after log.
abbrev addon (V:Type)[DecidableEq V][Fintype V]: Poly (MergeProof.Ribbon.Bud V) →ₐ[ℂ] Poly (MergeProof.Ribbon.Bud (Option V)):=Many.feed (fun _:V=>1) hole
noncomputable def capper (p:Poly B):Poly Z:= Poly.pass (Poly.send ((Z).fire none) 1) * addon V p
abbrev allP (V:Type)[DecidableEq V][Fintype V] : (MergeProof.Ribbon.Bud V).Mode:=⟨univ,mem_univ _⟩
-- preserves read. No changing estimation if removing other vals.
lemma jolt (s:(B).Mode) (c:ℂ): let j:(Z).Mode:=⟨s.val.image some, Finset.mem_univ _⟩; addon V (Poly.send s c)=Poly.send j c:=by
   intro j; have ht:Many.Lit (Z) some s.val:= ⟨Finset.mem_univ _,Option.some_injective _|>.injOn⟩; rw [addon,mouth,Many.move,dif_pos ht,Finset.prod_const_one,one_mul]; rfl
private lemma ontoP(p:Finset V): (p.image some)∪{none}= (univ:Finset (Option V)) ↔ p=univ:=by
   constructor
   · intro hp; ext x; simp only [mem_univ,iff_true]; have he: some x∈ p.image some ∪ {none}:=hp.symm ▸ mem_univ _; simpa using he
   rintro rfl; ext x; cases x <;> simp
lemma crown (p:Poly B): (capper p).part (allP (Option V))=p.part (allP V):=by
   let q:= allP (Option V); let o:=allP V; let Q:= (Z).fire none
   let Y:= Poly.send Q 1
   have h': (capper p).part q=(addon V p).part q+ (Y*addon V p).part q:=by rw [capper,pass_send (c:=(1:ℂ)) ?_,add_mul,one_mul,Poly.part_plus]; change ({none}:Finset (Option V)).Nonempty;exact singleton_nonempty _
   let a:(B).Mode→ (Z).Mode:=fun i=>⟨i.val.image some,mem_univ _⟩; have hp1(i:(B).Mode):Poly.merges Q (a i) q ↔ i=o:=by unfold Poly.merges; rw [show Disjoint Q.val (a i|>.val) ↔ True from by simp [a,Q,Census.fire],true_and, union_comm]; change (i.val.image some) ∪{none}=univ ↔ _; rw [ontoP]; change i.val=o.val ↔ _; exact Subtype.ext_iff.symm
   have hp2 : addon V p=∑ i:(B).Mode,Poly.send (a i) (p.part i):=by
       nth_rw 1 [← Poly.studs p,map_sum]; exact sum_congr rfl fun i _=> jolt i _
   rw [show allP (Option V)=q from rfl,h',hp2,mul_sum,Poly.part_sum,show ∑ x:(B).Mode, Poly.part (Poly.send (a x) (p.part x)) q=(0:ℂ) from ?_, Poly.part_sum,zero_add]
   · have hc(i:(B).Mode): (Y* Poly.send (a i) (p.part i)).part q=if i=o then p.part i else 0:=by rw [show Y*_=Poly.prod Y _ from rfl,show Y= _ from rfl, Poly.cart];simp only [hp1,one_mul] -- let Y
     simp_rw [hc]; rw [sum_ite_eq',if_pos (mem_univ _)]
   apply sum_eq_zero; intro i _; rw [Poly.part_send,if_neg ?_]; rintro h; have h':none∈(a i).val:= h ▸ (mem_univ _); simp [a] at h'
abbrev roots (x:Site n)(o:V→Site n)(j: O):= Option.elim j x o
abbrev branch (V:Type): Fibers (Option V) Unit:=⟨fun _=> (),fun _=>none, fun _=>rfl⟩
def stick (v:V→ℂ) (i:Option V):ℂ:= Option.elim i 1 v
def seed (x:Site n)(o: V→Site n)(v:V→ℂ)(U:Support n→ Config G n→ Poly B)(K:Box n→ Config G n→ Poly B): Fibers.Salt Unit O (branch V) G n := ⟨roots x o,stick v,fun p U'=> addon V (U p U'),fun p U=> addon V (K p U)⟩
lemma swept (v:V→ℂ): Mach (Z) (stick v)= Poly.send ((Z).fire none) 1 + addon V (Mach (B) v):=by
   rw [Mach,Fintype.sum_option,Mach,map_sum]; congr 1; exact sum_congr rfl fun i _=> by dsimp only [addon];rw [feed_fire,one_mul]; rfl
lemma intake (x:Site n)(o:V→Site n)(v:V→ℂ)(H:Support n→ Config G n→ Poly B)(K:Box n→ Config G n→ Poly B)(R:Rep G n)(hs:∀ i U,(H i U).part (B).quiet=0)(U) : (capper (play R (B) K (fun U=>Mach (B) v+∑ i,H i U) U))= Fibers.Salt.income R (seed x o v H K) U:=by
     let Q:=seed x o v H K; let Y:=fun U=>Mach (B) v+∑ i,H i U; let Y':=fun U=> addon V (Y U)
     have hp(U): (Y U).part (B).quiet=0:=by unfold Y; simp only [Poly.part_plus,mute,Poly.part_sum,hs,Finset.sum_const_zero,add_zero] -- fix
     unfold capper; rw [show addon V (play R (B) K Y U)=play R (Z) Q.river Y' U from congr_fun (Many.carry_play _ _ hp) _]; let V':= (Z).fire none
     have he : (Y' U).part (Z).quiet=0:= by exact (Many.feed_quiet ..).trans (hp _)
     change Poly.pass _ * play R (Z) Q.river Y' U= play R (Z) Q.river _ U; simp only [play]
     rw [show Q.pepper=stick v from rfl, swept, add_assoc]
     have hh: addon V (Mach (B) v)+∑ i,Q.air i U=Y' U:=by unfold Y' Y; rw [map_add,map_sum]; rfl
     rw [hh]; let z:= Poly.send V' (1:ℂ); have h:z.part (Z).quiet=0:= by unfold z V'; simp [( (Z).fire_hot _).symm]
     rw [pass_add h he, mul_smul_comm, mul_assoc]
set_option quotPrecheck false
local notation "Y"=> C.path.rep N p
local notation "K"=> C.path.levels
local notation "P0"=> C.path.levels.budget i
local notation "Δ"=> Legato.Bandage.renal C.path.levels i
-- V can be empty: include dummy to keep nonempty (birth const read). Focus o arbitrary. ALWAYS k≥1.
local notation "L"=> Site (C.side i p)
variable (x : Site (C.side i p)) {P:V→Three G (C.side i p)} {H: Series C p i (MergeProof.Ribbon.Bud V)}{o:V→Site (C.side i p)}{J t:ℝ} (h:C.Makes){D:Address.Rail C}(hv:Cater C D) -- D undeclared
variable (hi:i≤N)
def boon (C:Family G) (k i d:ℕ) (v:ℝ) :ℝ:= ((Fibers.Salt.tow (fun _:Unit=> min 1 v) ((C.path.levels.budget i).supportExponent+1/2) (Legato.Bandage.renal C.path.levels i/(k+1)) d) ())^(k+1) -- hull radius d
local notation "w!"=> boon C (Fintype.card V) i d J
local notation "δ"=> (P0).supportExponent
local notation "r'"=> roots x o
local notation "M"=> apron (K) i
include hi h hv
set_option maxHeartbeats 200000
lemma rope (hf:0 < i)(he:Furls C.path.levels i t)(hJ:0 < J) (ho:Occupancy (roots x o) (apron C.path.levels i))(hk:∀ v:V,coverNumber ((C.path.levels.budget i).B) ({x,o v}:Support (C.side i p)) ≤ d)(hd: 1 ≤ d)
    (ha:Alcove (C.path.rep N p i) P H o (fun _=>J) t (Legato.Bandage.renal C.path.levels i) (1/2)): 0 < (boon C (Fintype.card V) i d J) ∧ ∃ T:Three G (C.side i p), Useful (C.path.rep N p i) T ∧ MergeProof.Float.Blade (C.path.rep N p i) x T.2.1 (profile ((C.path.rep N p i).activities) T.2.2) 0 (4*(1/(boon C (Fintype.card V) i d J))) ∧ T.1=(fun U=> (H U).part (allP V)) :=by
    have hC:= h.wilson.represents N p i hi; let Q:= Y i
    have hΨ : Arsenal (Y i):=by
       cases i with
       | zero=> omega
       | succ n=> obtain ⟨z,y,hC,-⟩:= hv.tiers n N p (Nat.lt_of_succ_le hi); exact hC.publishes.contact
    obtain ⟨F,K',ψ,g,hF,hK,hX,hW,-,hz,hR,-,hH⟩:=ha.chamber
    let R:= seed x o g F K'; let u₀:=fun _:Option V=>min 1 J; have hw':0 < min 1 J:=lt_min zero_lt_one hJ; let u:=w!
    let n:=Fintype.card V; obtain ⟨ht,hΔ,hD,hM,hχ,hS,hc⟩:=he.eye
    have hl:0 < n+1:=by positivity
    let U₁:= Fibers.Salt.tow u₀ (δ+1/2) (Δ/(n+1:ℕ)) d; have h_Y(j:O):0 < U₁ j:= by unfold U₁ Fibers.Salt.tow u₀; positivity
    have hP(j:V): min 1 J* ‖(fun _:V=>(1:ℂ)) j‖≤ J:= by rw [norm_one,mul_one]; exact min_le_right ..
    have hy: ∀ j:Unit,(branch V).contents j=univ:= by simp [contents]
    have hPt(i):0 < u₀ i:= hw'
    have hu(v:Unit): u=∏ j∈ (branch V).contents v,U₁ j:=by unfold u boon; rw [hy]; let f:= U₁ none; rw [show U₁=(fun _=> f) from funext fun _=>rfl, Finset.prod_const,Finset.card_univ,Fintype.card_option]; dsimp [f,U₁,Fibers.Salt.tow,n,u₀]; rw [Nat.cast_add,Nat.cast_one]
    have hp_u:0 < u:= (hu ()).symm ▸ Finset.prod_pos (fun i _=> h_Y _)
    have h_f: Q.p=P0:=hC.vac
    let q':= Ribbons.Fibers.reap (branch V); have hx: Q.activities.Valid Q.p _ _:=hC.good.labels
    have hz0(K'':O): u₀ K'' * ‖R.pepper K''‖ ≤ 1:=by
       cases K'' with
       | none=> change _*‖(1:ℂ)‖≤_; rw [norm_one,mul_one]; exact min_le_left ..
       | some k=> exact (mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) J) (norm_nonneg (g k))).trans ((hz k).trans (by norm_num))
    have hM':R.Breeze Q.p.threshold:= ⟨fun j=> carry_burns hole _ (show o=roots x o ∘ some from rfl) (hX _),fun j=> carry_flow hole _ (show o=roots x o ∘ some from rfl) (hW _)⟩
    have hh(j:Option V): coverNumber Q.p.B ({R.focus ((branch V).bunch j),R.grain j}: Support (C.side i p)) ≤ d:=by
       rw [h_f]; cases j
       next=> change coverNumber _ ({x,x}:Support (C.side i p))≤d; rw [Finset.insert_eq_of_mem (Finset.mem_singleton_self x)]
              let a:= (P0).B; have ht: coverNumber a (Lattice.halo 0 {x}) ≤ 1:=by simpa using Corona.tile x 0 _ ((P0).B_pos)
              exact (Corona.cover_mono (Lattice.halo_subset ..) _).trans (ht.trans hd)
       next j=> exact hk _
    have hu'(v:Unit): u=∏ j∈ (branch V).contents v,Fibers.Salt.tow u₀ (Q.p.supportExponent+1/2) (Δ/(n+1:ℕ)) d j:=by rw [h_f]; exact hu _
    obtain ⟨l,hL⟩:= Fibers.Salt.materialize R M d (Δ) 1 1 _ hl hΨ hM' hx (fun j U=> (Many.feed_quiet ..).trans (hR j U)) hPt ho zero_le_one hz0 Q.p.B_pos hΔ hD hh (show 0≤(1/2:ℝ) by norm_num) (carry hole (fun _=>1) hF hP (fun _=> hJ) hPt) (carry hole (fun _=>1) hK hP (fun _=>hJ) hPt) (fun i=> by rw [hy]; simp [n]) (fun j=> (Tour.bright (C.path) ‹C.Makes›.wilson N p i hi j).ne') (w:=fun _=>u) hu' (show _ from h_f.symm ▸ hS) (show _ from h_f.symm ▸ hc)
    obtain ⟨hV,hD⟩:= hL.foot (); let f:= R.debt Q.p.threshold (); let T':= (coin Q f (l ()),f,l ()); refine ⟨hp_u,T',⟨hV,rfl,MergeProof.Float.spill_in hD hC.good hV⟩, hD,?_⟩
    funext j; have hA:= (hL.served.relay (fun i=> (hL.foot i).1) hx j).1 ()
    change coin Q f _ j=_
    change (Fibers.Salt.income Q R j).part ((branch V).plena ((Ribbon.Bud Unit).fire ())) = coin Q f (l ()) j at hA
    rw [← hA,show (branch V).plena ((Ribbon.Bud Unit).fire ())=allP (Option V) from Subtype.ext (by simp [plena,Census.fire,hy]),hH, ← show capper (play Q (B) K' (fun U=>Mach (B) g+∑ i,F i U) j)=Fibers.Salt.income Q R j from intake x o g F K' Q (fun z U=>(hX z).sil U) j,crown]
end Root
end YM.RG05Readout.Petra
