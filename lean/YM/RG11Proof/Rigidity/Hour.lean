import YM.RG11Proof.Rigidity.Prism.Frame

/-!
# Real word presentations (and associated graded covectors on the group)
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity
open Maxwell Maxwell.Free Crowd Prism
open scoped BigOperators Classical

abbrev Article (G : Gauge) := List (Dart G)
abbrev Cast (G : Gauge) := List (ℝ × Article G)
def issue {G:Gauge} (Y : Cast G) (q : Article G→ℝ) := (Y.map fun i=>i.1*q i.2).sum

variable {G : Gauge}

-- advance local actors and qualify engineering weights

def travel (z : E4) (i : Article G) : Word G := i.map fun q=> Pig.mk z q

def ceilingG (i : Article G) := cargo (travel 0 i)
lemma travels (z : E4) (i : Article G) : cargo (travel z i)=ceilingG i := by simp [ceilingG,travel,cargo,List.map_map,Function.comp_def,weightF]

def ticket (z : E4)(C : Cast G): Crowd G:= C.map (fun it=> (it.1,travel z it.2))

lemma ticket_read (x : E4) (C : Cast G) (m : Word G→ℝ) : (ticket x C).asks m=issue C (fun i=>m (travel x i)):= by simp [issue,ticket,asks,List.map_map,Function.comp_def]
lemma ticket_live {x : E4}{S:Finset E4}(h:x∈S)(C : Cast G): (ticket x C).Live S:= by
  rintro w hw p hp
  obtain ⟨i,hC,rfl⟩:= List.mem_map.mp hw; obtain ⟨q,hq,rfl⟩:= List.mem_map.mp hp; exact h

def times (W T : Crowd G) : Crowd G:= W.flatMap (fun t=>T.map (fun i=> (t.1*i.1,t.2++i.2)))

lemma times_read (W T:Crowd G) (m:Word G→ℝ): (times W T).asks m=W.asks (fun i=>T.asks (fun t=>m (i++t))) := by
  induction W with
  | nil=>rfl
  | cons a W ih=>
    rw [show times (a::W) T= (T.map (fun i => (a.1*i.1,a.2++i.2)))++times W T from by simp [times],ask_append,ih,ask_one]
    congr 1; clear ih; induction T with
    | nil=>simp
    | cons q T ht=>
      rw [List.map_cons,ask_one, ask_one,ht]
      dsimp only; ring

def ceilingC (W : Crowd G) (N:ℕ) := ∀ w∈W,cargo w.2≤ N

lemma times_live {W T:Crowd G}{S : Finset E4}(hW : W.Live S)(hT:T.Live S) : (times W T).Live S:= by
  rintro w hw i hi
  obtain ⟨t,ht,hh⟩:= List.mem_flatMap.mp hw
  obtain ⟨b,hb,rfl⟩:= List.mem_map.mp hh
  exact (List.mem_append.mp hi).elim (hW t ht i) (hT b hb i)

lemma cargo_add (a b : Word G) : cargo (a++b)=cargo a+cargo b:= by simp [cargo,List.sum_append]
lemma times_limit {W T:Crowd G}{a b : ℕ}(h : ceilingC W a)(hk : ceilingC T b): ceilingC (times W T) (a+b) := by
  intro w hw
  obtain ⟨t,ht,hh⟩:=List.mem_flatMap.mp hw; obtain ⟨q,hq,rfl⟩:= List.mem_map.mp hh
  change cargo (_++_) ≤ _; rw [cargo_add]; exact add_le_add (h _ ht) (hk _ hq)

abbrev System := G.ColorIndex → (j : ℕ) → Sheet j
-- Top covector. Real coefficient convention and no re-weighting by factorials.
def topSample (Y : Cast G) (N : ℕ) (q : System (G:=G)) (M : Mirror G) := issue Y fun i =>
    if ceilingG i=N then (List.map (fun a:Dart G=> ∑ s:G.ColorIndex, M (a.tone,s)*a.mode (q s a.degree)) i).prod else 0
lemma samples_cont (Y:Cast G)(N:ℕ)(q:System (G:=G)): Continuous (topSample Y N q) := by
  have ht (i : Article G) : Continuous (fun M:Mirror G=> (List.map (fun a:Dart G=> ∑ s:G.ColorIndex, M (a.tone,s)*a.mode (q s a.degree)) i).prod) := by
    induction i with
    | nil=> exact continuous_const
    | cons a i ih=>
      change Continuous (fun M : Mirror G => (∑ s:G.ColorIndex, M (a.tone,s)*a.mode (q s a.degree))*_); apply Continuous.mul _ ih
      exact continuous_finsetSum _ fun s _=> ((PiLp.proj (𝕜:=ℝ) 2 (fun _: G.ColorIndex×G.ColorIndex=>ℝ) (a.tone,s)).continuous).mul continuous_const
  induction Y with
  | nil=> exact continuous_const
  | cons a l ih=>
    change Continuous (fun M=> a.fst*(if ceilingG a.2=N then _ else _) + topSample l N q M)
    apply Continuous.add _ ih; apply Continuous.mul continuous_const; split_ifs; exact ht _; exact continuous_const

lemma top_tick (x : E4)(Y : Cast G) (N : ℕ)(Θ:G.ColorIndex→Stream)(M : Mirror G) :
    (ticket x Y).asks (air M Θ N)=topSample Y N (fun i=> Θ i x) M := by
  rw [ticket_read]; unfold topSample
  congr 1; funext i
  unfold air; rw [travels]
  simp [airRaw,hue,travel,List.map_map,Function.comp_def,dial_wind]

lemma top_times {W T : Crowd G}{i j : ℕ}(h:ceilingC W i)(ht:ceilingC T j) (Θ:G.ColorIndex→Stream)(M:Mirror G):
    (times W T).asks (air M Θ (i+j)) = W.asks (air M Θ i) * T.asks (air M Θ j):= by
  have he (a b : Word G)(ha : cargo a ≤ i)(hb:cargo b≤j): air M Θ (i+j) (a++b)=air M Θ i a*air M Θ j b := by
    unfold air; rw [cargo_add]
    rw [if_congr (show cargo a+cargo b=i+j ↔ cargo a=i ∧ cargo b=j by omega) rfl rfl]
    split_ifs <;> simp_all [Prism.hue,airRaw]
  rw [times_read,mul_comm,← ask_mul]
  refine told W _ _ (fun w hw=> ?_)
  rw [told T _ (fun v=>air M Θ i w.2 * air M Θ j v) (fun t hu=>he _ _ (h _ hw) (ht _ hu)),ask_mul]; ring

end YM.RG11.Rigidity
