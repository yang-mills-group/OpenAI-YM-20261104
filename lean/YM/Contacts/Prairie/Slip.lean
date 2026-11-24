import YM.Contacts.Prairie.Inn
import YM.Contacts.Barrage.Piscine
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
open Oasis Milling.Spark
variable {r v l k:ℕ}
abbrev seedling (j r:ℕ) := @Sub.sub (Field (Fin r) (Node (Mixed G (e.flag s)))) _ (if r=j then Spark.sparkles (e.flag s) e.Q r else 0) (show Field (Fin r) (Node (Mixed G (e.flag s))) from (if r=j+2 then fireworks (e.flag s) e.K G r else 0))
abbrev early:= clan e.Q (e.flag s) e.K (e.port p)
abbrev Lift (F:Field (Fin r) (Node (Dye G))):= lifts (e.A p s) F
lemma givens (h:i≠0) (r:ℕ): e.early p s i r=e.seedling s i r-lifts (e.planter s) (e.port p i r):= by
   unfold early clan compote; rw [if_neg h]; let P:=e.flag s; let u:Field (Fin r) (Node (e.White s)):= if r=i then Spark.sparkles P e.Q r else 0; let v:Field (Fin r) (Node (e.White s)):= if r=i+2 then fireworks P e.K G r else 0; let Z:=lifts (e.planter s) (e.port p i r); change u+-(v+Z)= (u-v)-Z; abel
def beet := gathering (plane (e.raw p s)) (e.early p s)
def drove (w r:ℕ) := (∑ j∈Finset.range (3*w),e.beet p s (j+1) w r)+ e.seedling s w r
def board (i r:ℕ):= e.Lift p s (flare G i r) - hoist (plane (e.beam p s)) (e.drove p s i r)
lemma earnedDrive (h:i≠0)(r:ℕ): massaged (plane (e.raw p s)) (e.early p s) i r=e.drove p s i r - lifts (e.planter s) (e.port p i r):= by unfold massaged drove beet; rw [sum_range_succ', gathering_start,e.givens p s h]; abel
variable {S:Boom}{e s p} (T:e.License S ζ)(hs:s∈S)
include T
lemma beet_zero (h:OK S p)(z v:ℕ)(hh:j=0∨j+2<v): e.beet p s z j v=0:= ((clan_shape G e.Q (e.port p) (T.prosper h).blazing.frame.toShaped).bounded _ z).thin j v hh
omit T
lemma stock_bool (s:Step)(X Y:Type): Ripple (terrain ζ X) (terrain (2*ζ) Y) (access s.L (2*ζ)):= influx (step_reserved s ζ)
def Spatters (S:Boom)(e: Parcel G)(s:Step) (ζ:ℝ≥0) (F:Word→Field (Fin r) (Node (e.White s))):Prop:= Fleet S (terrain (2*ζ) _) F
lemma seeded : Spatters (r:=r) S e s ζ (fun _=> e.seedling s j r):= by
   unfold seedling Spatters; refine Fleet.sub (f:=fun _=> if r=j then Spark.sparkles (e.flag s) e.Q r else 0) ?_ ?_; by_cases he:r=j; swap; · simp_rw [if_neg he]; exact Fleet.fzero
   · simp_rw [if_pos he]; exact Fleet.given (aboard_summed (Spark.templates G (e.flag s)) _ _)
   by_cases ht:r=j+2; swap; · simp_rw [if_neg ht]; exact Fleet.fzero
   simp_rw [if_pos ht]; exact Fleet.given (aboard_summed _ _ _)
variable (h:e.Last (S:=S) (ζ:=ζ) k i r)
include h in
lemma earlier (ht:Past i r j v): Spatters S e s ζ (fun p=>e.early p s j v):= by
   by_cases he:j=0; · exact Holds.eq Fleet.fzero (fun p _=> by unfold early clan compote; rw [if_pos he])
   refine Holds.eq (g:=(fun p=>e.early p s j v)) (Fleet.sub (l:=terrain (2*ζ) _) (f:=fun _=>e.seedling s j v) seeded (Threads.lift License.planted (stock_bool s (Dye G) (e.White s)) (Fleet.weaken (k:=terrain ζ _) ((h _ _ ht).ofPort) bath_terrace))) (fun p _=> (e.givens p s he _).symm)
include T hs h
lemma dues (d l w:ℕ)(hw : Past i r w l ∨ (w=i∧l=r∧d≠0)) : Spatters S e s ζ (fun p=> e.beet p s d w l):= by
   induction d using Nat.strongRecOn generalizing w l with| _ d ih=>
   unfold Past at hw; cases d; · simp only [beet,gathering_start]; exact Parcel.earlier h (by unfold Past; omega)
   rename_i d; simp_rw [beet,gathering_next]; apply Fleet.smul; unfold wake; refine Fleet.add (Climb.dose (F:=fun p=>e.beet p s d w (l+2)) (T.raw_bill hs) (ih d (by omega) _ _ (by unfold Past; omega))) (Fleet.sum (antidiagonal w) ?_); intro p hp; apply Fleet.sum (antidiagonal d); intro q hq; unfold listPay; apply Fleet.sum (antidiagonal l); intro j hj
   have hp:= mem_antidiagonal.mp hp; have hq:=mem_antidiagonal.mp hq; have hj:=mem_antidiagonal.mp hj; by_cases he:p.1=0; · exact Holds.eq Fleet.fzero (fun n h=> (light_close_left _ (Parcel.beet_zero T h _ _ (Or.inl he))).symm)
   by_cases hk:p.2=0; · exact Holds.eq Fleet.fzero (fun n h=> (light_close_right _ (Parcel.beet_zero T h _ _ (Or.inl hk))).symm)
   exact Climb.link (T.raw_bill hs) (ih _ (by omega) _ _ (by unfold Past; omega)) (ih _ (by omega) _ _ (by unfold Past; omega))
lemma drove_law : Spatters S e s ζ (fun p=>e.drove p s i r):= Fleet.add (Fleet.sum _ fun j _=>dues T hs h (j+1) r i (Or.inr ⟨rfl,rfl,by omega⟩)) seeded
lemma board_law : Fleet S (bath ζ k _) (fun p=>e.board p s i r):= T.pa k (Fleet.sub (Threads.lift (R:=fun _=>flare G i r) (T.round_trips hs) (stock_bool s _ _) (Fleet.given ((flare_purse G ζ).shelter i r))) (Threads.lift (T.beam_bill hs) fareFoot (drove_law T hs h)))
omit h in
lemma hailed {F:Field (Fin r) (Node (Dye G))}[NeZero r]{b:ℝ}(hp: Rooted (terrain ζ _) F b)(hf:∀ z:Cover,Mirrored (backpack z) F): hoist (plane (e.beam p s)) (lifts (e.planter s) F)=lifts (e.A p s) F:= by
   let t:=s; let s:=(2*ζ); let P:=e.flag t; let R:=e.beam p t; let v:=e.A p t; let S(k:Side):=sprig P e.K k; let f(k:Side):=k*P.L; let W(k:Side):=printShadow F (f k); let Z(k:Side):= hoist (installed (S k).ratio (adopt (Cellar G P.L) (Dye G))) (W k); let H(k:Side):=hoist (Row.acts R k) (Z k); let X(k:Side):=hoist (installed (S k).ratio v) (W k);
   have ht(k:Side): Shadow (lower (f k)) F (W k):= printFeeds (heritage hf (f k)); have h₁ : Row.strip (e.planter t) (s:ℝ) 1:= adopt_cost _ _ _; have he:=ledgers (R:=e.planter t) h₁ zero_le_one; let l:= ζ; have hx : Ripple (terrain l (Dye G)) (terrain s (e.White t)) (access (t.L) s):= influx (step_reserved t ζ); have hk:= hoist_pay hx he hp; obtain ⟨b,hb,h⟩:= T.base _ hs; have hu:= ledgers (α:=Dye G) (h p).feed hb; have hR:= flight_stem (sky_shape (U:=e.A p t) (h p).feed hb) (add_nonneg zero_le_one hb);
   refine receives (A:=H) (B:=X) (hoist_pay fareFoot hR hk) (hoist_pay (influx (step_reserved t ζ)) hu hp) (fun m=>?_ ) (fun m=>funext fun y=>?_ )
   · exact ⟨hoist_period fareFoot hR hk (hoist_period hx he hp (ht m) (st_new (S m).ratio (e.planter t))) (row_ship R m), hoist_shape,hoist_period (influx (step_reserved t ζ)) hu hp (ht m) (st_new (S m).ratio v),hoist_shape⟩
   let U:= R.acts m*ᵥ y; let V:= installed (S m).ratio v; let z:= V*ᵥ y
   calc
      design (H m) y = design (Z m) U:= hoist_read _ _ _
      _ = design (W m) (shave (S m) G *ᵥ U):= by rw [← offspring_paid (S m)]; exact hoist_read _ _ _
      _ = design (W m) z:= by
          rw [shaved,(show U=weave (S m) (y,z) from ?_),blooms]; unfold U; rw [show R.acts m=Forge.sky (S m) G V from skytop (G:=G) (S m) v]; exact sky_pass ..
      _ = _:= (hoist_read _ _ _).symm
lemma kick_formula [NeZero r] (hp:OK S p)(hi:i≠0): e.kickoff p s i r=e.Lift p s (e.dust p i r)+ e.board p s i r:= by
   let X:= e.port p i r; let V:=flare G i r; let d:=e.drove p s i r; obtain ⟨_,_,H⟩:= (show Fleet _ _ _ from drove_law T hs h).1; obtain ⟨_,_,hc⟩:= License.planted (e:=e) (s:=s) (ζ:=ζ) (S:=S)|>.1; obtain ⟨_,_,hT⟩:= T.round_trips hs|>.1; obtain ⟨_,hZ⟩:= (T.banks hp).2; obtain ⟨_,_,hU⟩:= T.beam_bill hs|>.1
   let Y:=lifts (e.planter s) X; let S':= hoist (α:=Node (e.White s)) (r:=r) (plane (e.beam p s)); let K:= e.Lift (r:=r) p s; let hv:= (flare_purse G ζ).shelter i r; let hx:= (hZ.shelter i r).weaken (terrain_le T.down) le_rfl; let hy:= hoist_pay (stock_bool (ζ:=ζ) s _ _) (hc p hp) hx
   unfold kickoff oil caravan kiss; rw [if_neg (NeZero.ne r), mintage, if_neg hi]; change - S' (massaged (plane (e.raw p s)) (e.early p s) i r) = K (X-V)+(K V-S' d); rw [e.earnedDrive p s hi r]; change - S' (d-Y)=_; have hr:S' (d-Y)= S' d-S' Y:= hoist_sub fareFoot (hU _ hp) (H p hp) hy; have hn: K (X-V)=K X-K V:= hoist_sub (stock_bool _ _ _) (hT p hp) hx hv; rw [hr,hn,show S' Y=K X from hailed T hs hx fun z=> (T.prosper hp).blazing.frame.here z i r]; abel
end Parcel
end
end YM.Contacts.Prairie
