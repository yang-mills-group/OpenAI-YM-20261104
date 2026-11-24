import YM.WilsonCoeffUV.Product.Report.Family
/-!
# Auxiliary block windows
We can use the existing `Levels` estimates for arbitrary integer-indexed finite
windows with constant blocking & smoothing, and even with one switch **meeting
the smoothing/monotonicity convention**. Increase J by one for the finer
plateau if L changes. This permits a switch of powers of primes too. We do
not supply switched procedures violating the quadratic conditions in the
pinned library. We retain the same K. All pre/enlargement asks register as
usual. Post L and theta gates in our proofs are solely bills on the auxiliary
clock (`BASIC`); `bar` and `hatBeta` and period list of the big padded `Levels`
are irrelevant to finite formulas. Padded slot translation duly accounted.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.WilsonCoeffUV.AuxPlates
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil Power
open Embroider Precision Exterior Source Source.Drops Labels WardBin Cosmos Bulb Realm Fountain PathCost Supply Ticket Shard Plan Mer Patrol
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
open Real
variable {G:Gauge}{F' D':ℕ→ℕ} {p:Sheet G}{Q:Rolls p}{Ω:Protection Q}
variable {Y:Delays Ω}{o:Bar Y}{B: Supply.Wait o} {A:Levels G} {s t j l k n a i m:ℕ}

/-- Shift after c OLD steps. Hold first stage at level start+n+2 when there's no
requested switch within the span; this preserves the same width gates through
the whole interval. On switches width may be lowered before buying both lengths. -/
def Walk (A: Levels G) (first c start n:ℕ): Prop:=∀ i, i≤ n→ A.clock.J (start+i)= if i≤ c then first else first+1
lemma Walk.block (H: Walk A p.first t s n)(P: Paid B A)(i:ℕ)(h:i<n): A.S.block (s+i)= if i< t then Q.L p.first else Q.L (p.first+1):=by
    rw [← A.fits.sameFactor, P.lengths,Nat.add_assoc,H (i+1) h]; split_ifs<;>first | rfl | omega
lemma delayedRoom (Y:Delays Ω):∃ z:ℕ→ℕ,∀ (j:ℕ) (v:ℝ), (z j:ℝ)* log 3 ≤ v → Y.betaEntry j ≤ exp (exp (v-1)):=by
    have h:Tendsto (fun x:ℝ=> exp (exp (x-1))) atTop atTop:= by
        apply Real.tendsto_exp_atTop.comp; apply Real.tendsto_exp_atTop.comp; exact tendsto_id.atTop_add (tendsto_const_nhds (x:=(-1:ℝ)))
    choose x X using fun j=> eventually_atTop.mp (h.eventually_ge_atTop (Y.betaEntry j)); choose n N using fun j=> exists_nat_ge (x j / log 3)
    exact ⟨n,fun j v q=> X j v (( (div_le_iff₀ (log_pos (by norm_num))).mp (N j)).trans q)⟩
lemma scaleTape (s:Schedule)(i n:ℕ) : (n:ℝ)*log 3 ≤ s.scale (i+n)-s.scale i:=by
    induction n with
    | zero=> simp
    | succ n ih=> push_cast; have h:log 3 ≤ s.scale (i+n+1)-s.scale (i+n):= arch_pos ..; rw [←add_assoc i]; linarith

def extendedY (V:ℝ)(S:Schedule)(k j:ℕ):ℝ:= V+S.scale (max j k)-S.scale k
lemma y_floor (V:ℝ)(S: Schedule): V≤extendedY V S k j := by
    unfold extendedY; have h:= scales S (le_max_right j k); linarith
lemma y_plate (V:ℝ)(S:Schedule)(q:j≤k): extendedY V S k j=V:=by
    rw [extendedY,max_eq_right q]; ring
lemma y_aged (V:ℝ)(S:Schedule)(q:j≤ l): extendedY V S k l ≤ extendedY V S k j+(S.scale l-S.scale j):=by
    have h:= scales S q
    rcases le_total l k with t|t; · rw [y_plate _ _ (q.trans t),y_plate _ _ t]; linarith
    rcases le_total j k with s|s
    · rw [y_plate _ _ s,extendedY,max_eq_left t]; linarith [scales S s]
    rw [extendedY,extendedY,max_eq_left s,max_eq_left t]; linarith

lemma rooms (B0:ℕ → ℕ): ∃ b:Supply.Wait o,b.window=(fun j _=>B0 j):=by
    refine ⟨⟨0,fun j _=>B0 j,fun j=>?_,0⟩,rfl⟩
    exact tendsto_const_nhds.div_atTop tendsto_id

/-- k = last OLD smoothing level -/
lemma anchorLast (x:Paid B A) : ∃ k:ℕ, A.clock.J k=p.first ∧ A.clock.J (k+1)=p.first+1:=by
    obtain ⟨b,h⟩:= eventually_atTop.mp (A.fits.deep.eventually (eventually_ge_atTop (p.first+1))); have he: ∃ i,p.first<A.clock.J i:=⟨b,h b le_rfl⟩
    let n:= Nat.find he; have hv:p.first<A.clock.J n:= Nat.find_spec he
    have hy:n = n-1+1:= Eq.symm (Nat.sub_add_cancel (show 1≤n from Nat.pos_of_ne_zero (fun z=> by rw [z,x.firstZero] at hv; omega)))
    have hβ:A.clock.J (n-1)=p.first:= le_antisymm (le_of_not_gt (fun j=> by have h:n ≤ n-1:= Nat.find_min' he j; omega)) (x.firstZero ▸ A.fits.mono (by omega))
    refine ⟨n-1,hβ,?_⟩
    have ht:= A.fits.stepSlow (n-1); rw [hβ] at ht; exact le_antisymm ht (hy ▸ hv)

-- window Ready stage. m ≥ k. explicit gate. `z` may include any desired extras.
theorem finite_plates (g:G.Simple)(o:Bar Y):∃ C:ℝ,1≤C ∧ ∀ n c:ℕ,c≤n→ ∃ (A:Levels G)(start:ℕ) (B:Supply.Wait o),Walk A p.first c start n∧ Paid B A ∧ BasicBill Y A (extendedY C A.S (start+n)) start:=by
    choose z h using delayedRoom Y
    let C:ℝ:= max 1 (max ((z p.first:ℝ)*log 3) ((z (p.first+1):ℝ)*log 3))
    have hC:1≤C:=le_max_left ..; have he:= lt_of_lt_of_le zero_lt_one hC
    refine ⟨C,hC,fun n c q=>?_⟩
    let w j:= n+z (j+1)+1; obtain ⟨b,hb⟩:= rooms (o:=o) w; obtain ⟨A,x⟩:= Supply.Wait.ready b g
    have ha j (q:p.first ≤ j) : ∃ k', w j≤k'∧ ∀ i,k'-w j ≤ i→i ≤ k'+w j → A.clock.J i=j:=by
        obtain ⟨K,_,v,t⟩:= x.run j q; rw [hb] at v t; exact ⟨K,v,t⟩
    obtain ⟨k,hk,ht⟩:= anchorLast x
    have hR i:i ≤ k↔ A.clock.J i=p.first:=by
        constructor; · exact fun p=> le_antisymm (hk ▸ A.fits.mono p) (x.firstZero ▸ A.fits.mono (Nat.zero_le i))
        intro h'; by_contra! hh; have h:A.clock.J (k+1)≤ A.clock.J i:= A.fits.mono hh; omega
    obtain ⟨d,hd,t⟩:= ha p.first le_rfl
    have hv:(w p.first)≤ k:= hd.trans ((hR d).2 (t _ (by omega) (by omega)))
    have hy:n≤k:= (show n≤w p.first from le_trans (Nat.le_add_right n _) (Nat.le_succ _)).trans hv
    let a:=k-c; let f:=p.first; have hl : a+c=k:= Nat.sub_add_cancel (q.trans hy); obtain ⟨l,hL,vL⟩:= ha (p.first+1) (by omega)
    have hp:k<l:=by have hh:= vL l (by omega) (by omega); specialize hR l; omega
    have hf:a+n ≤ l+w (p.first+1):=by have h:n≤w (p.first+1):= (Nat.le_add_right n _).trans (Nat.le_succ _); omega
    refine ⟨A,a,b,fun i t'=>?_,x,⟨x.kernel,x.lengths,?_,fun i _=> hC.trans (y_floor ..),fun i j _ z=> y_aged _ _ z ⟩⟩
    · split
      · rename_i h; exact (hR _).1 (by omega)
      rename_i h; apply le_antisymm; exact (A.fits.mono (show a+i ≤ l+w (p.first+1) by omega)).trans (le_of_eq (vL _ (by omega) (by omega))); exact ht ▸ A.fits.mono (by omega)
    intro m hm; let j:= A.clock.J (m+1); have hj:j ≥ p.first := x.firstZero ▸ A.fits.mono (Nat.zero_le _)
    apply h; by_cases v:j≤p.first+1
    · rcases (show j=p.first ∨ j=p.first+1 from by omega) with hx|hx
      · rw [show A.clock.J (m+1)=p.first from hx]; exact (((le_max_left ..).trans (le_max_right ..) : _ ≤ C).trans (y_floor ..))
      rw [show A.clock.J _=p.first+1 from hx]; exact ((le_max_right ..).trans (le_max_right ..) : _≤ C).trans (y_floor ..)
    obtain ⟨t,rfl'⟩:= (show ∃ t:ℕ, p.first<t∧j=t+1 from ⟨j-1, by omega⟩); obtain ⟨hv,v⟩:=rfl'; obtain ⟨u,v',V⟩:= ha t hv.le
    have hO:u+w t≤m:=by
        by_contra! he; have hp:A.clock.J (m+1) ≤ A.clock.J (u+w t):= A.fits.mono he; rw [V (u+w t) (by omega) (by omega)] at hp; change j ≤ _ at hp; omega
    have hu:k < u:=by have ht:=hR u; have he:= V u (by omega) (by omega); omega
    have hμ : a+n+z (t+1)≤m:=by have h: w t=n+z (t+1)+1:=rfl; omega
    have he:= scaleTape A.S (a+n) (z (t+1)); unfold extendedY; rw [show A.clock.J (m+1)=_ from v,max_eq_left (by omega)]; linarith [scales A.S hμ]
end YM.WilsonCoeffUV.AuxPlates
