# DiamondLinkAverage scope

Defines each pivot link as the actual Finset of unordered diamonds containing that vertex. Proves the exact incidence identity sum_p card(link p)=4D and existence of p with n*card(link p)≤4D on nonempty finite tournaments. No abstract incidence family replaces DiamondGap.Tournament.diamonds.

VERIFIED: direct Lean compilation to matching .olean succeeded; total_link_card and exists_small_link depend only on propext, Classical.choice and Quot.sound. Log: verification/diamond_link_average.log. Harmless unused simp warning remains. No full-project build is claimed here.
