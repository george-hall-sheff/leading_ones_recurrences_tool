from __future__ import division
import sys
import math

"""
    Code used to compute results in the paper "Analysis of the Performance of
    Algorithm Configurators for Search Heuristics with Global Mutation
    Operators".  This script computes the bounds on the coefficients of the
    linear term in the fitness of the indvidual in the (1+1) EA with mutation
    rate chi/n and then derives results about the monotonicity of the parameter
    space.
"""

def generate_li_ui(chi, psi, total_runtime):
    # Generate the bounds on the coefficients at the end of each period
    l = [0]
    u = [0]
    time_ui_exceeds_1 = 0

    for i in xrange(1, total_runtime):
        u.append(u[i-1]+((2*chi)/(psi*math.exp(chi*u[i-1]))))
        l.append(l[i-1]+((2*chi)/(psi*math.exp(chi*u[i]))))

        if (time_ui_exceeds_1 == 0) and (u[-1] > 1.0):
            time_ui_exceeds_1 = i

    return (l,u,time_ui_exceeds_1)

def latex_output(d):
    # Prints the coefficient bounds in a latex format
    for i in xrange(len(d[d.keys()[0]][0])):
        s = str(i) + " "
        for chi in sorted(d.keys()):
            to_add = "& [%.10f,%.10f] " % (d[chi][0][i],d[chi][1][i])
            s += to_add
        s += "\\\\"
        print s

def txt_output(d):
    # Prints the coefficient bounds in a plaintext format
    sys.stderr.write("Printing coefficient table...\n")
    for i in xrange(len(d[d.keys()[0]][0])):
        if (i%100000)==0:
            sys.stderr.write("Printing coefficient table... Current i: " + str(i) + "\n")
        s = str(i) + " "
        for chi in sorted(d.keys()):
            to_add = " %.10f %.10f" % (d[chi][0][i],d[chi][1][i])
            s += to_add
        print s

def find_best_chi_for_each_period(d, total_runtime):
    best_chis = []
    for i in xrange(1,total_runtime):
        bounds_i = {}
        bounds_i_minus_1 = {}
        best_chi = 0
        for chi in d.keys():
            bounds_i_minus_1[chi] = (d[chi][0][i-1], d[chi][1][i-1])
            bounds_i[chi] = (d[chi][0][i], d[chi][1][i])

        # Loop over all chis until we find one for which its lower bound at
        # time i-1 is greater than the upper bounds of all other chis at time
        # i. This means that this value of chi is ahead for all cutoff times
        # between the end of period i-1 and the end of period i.
        for chi in d.keys():
            decision = True
            lb = bounds_i_minus_1[chi][0]
            for chi1 in d.keys():
                if chi1 != chi:
                    if lb <= bounds_i[chi1][1]:
                        decision = False
            if decision:
                best_chi = chi
                break
        best_chis.append(best_chi)

    return best_chis

def verify_monotonicity(chi_list, d, time_opt_chi_exceeds_1):
    # Compute a list of the best value of chi for each period (i.e. the value
    # of chi which is ahead for the entire period i-1 to i)
    best_chis = find_best_chi_for_each_period(d, time_opt_chi_exceeds_1)
    mono_best_chis = {}

    # For each period, check whether the intervals covered by the intervals
    # decrease monotonically either side of the optimal chi
    for i in xrange(time_opt_chi_exceeds_1-1):
        if (i%10000)==0:
            sys.stderr.write("Verifying monotonicity of search space for i = " + str(i) + "\n")
        decision = False
        # Only execute if there *is* a best value for chi for this period
        if best_chis[i] > 0:
            decision = True
            # First check that the ranges covered by the intervals
            # corresponding to chis less than the optimum decrease
            # monotonically.
            bounds = {}
            less_than_best = [x for x in chi_list if x < best_chis[i]]
            for chi in less_than_best:
                bounds[chi] = (d[chi][0][i], d[chi][1][i])
            if len(less_than_best) > 1:
                pairs_to_check = zip(less_than_best[:-1],less_than_best[1:])
                for pair in pairs_to_check:
                    if decision and not (bounds[pair[0]][1] < bounds[pair[1]][0]):
                        decision = False

            # Now do the same for chis greater than the optimum.
            bounds = {}
            more_than_best = [x for x in chi_list if x > best_chis[i]]
            for chi in more_than_best:
                bounds[chi] = (d[chi][0][i], d[chi][1][i])
            if len(more_than_best) > 1:
                pairs_to_check = zip(more_than_best[:-1],more_than_best[1:])
                for pair in pairs_to_check:
                    if decision and not (bounds[pair[0]][0] > bounds[pair[1]][1]):
                        decision = False
        if decision == True:
            # If the monotonicity has been verified, then add this value of chi
            # to mono_best_chis
            mono_best_chis[i] = best_chis[i]
        else:
            mono_best_chis[i] = 0
    return mono_best_chis


def ineq(a,b,dab,alb,blb,bub,quantity_value_dict):
    epsilon = 0.00000000001
    # Save the actual value generated by the expression in the lemma for the
    # two configurations a and b. This is the quantity which must be less than
    # 1.

    numerator_minus_epsilon =              (2*b)                \
                                            /                   \
                              ((alb-bub) * math.exp(b*blb))
    numerator = numerator_minus_epsilon + epsilon

    denominator =           (2*a)                               \
                             /                                  \
                    ((1-alb)*math.exp(a))

    # Note that since quantity_value_dict is global, this value is added to the dict.
    quantity_value_dict[a][b] = numerator / denominator

    # Return True if the inequality holds, False otherwise
    return quantity_value_dict[a][b] <= 1.0

def check_ineq(d, chi_list, time_ui_exceeds_1_dict, first_chi_to_exceed_1, verbose):

    # This function checks the inequality in Lemma 4.6 that is used to verify
    # that once a configuration is far enough ahead of another and sufficiently
    # close to the optimum it remains ahead of or reaches the optimum before
    # the other configuration, with overwhelming probability.

    sys.stderr.write("Verifying inequality...\n")
    relevant_coeffs_dict = {}
    quantity_value_dict = {}
    for chi in chi_list:
        quantity_value_dict[chi] = {}
    # For each chi, creates a dict of the coefficient values for all chis when
    # that one's upper bound exceeds 1.
    for chi in chi_list:
        relevant_coeffs_dict[chi] = {}
        t = time_ui_exceeds_1_dict[chi]-1
        for x in chi_list:
            relevant_coeffs_dict[chi][x] = (d[x][0][t],d[x][1][t])

    for chi in chi_list:
        # For all chis `x' less than or equal to the optimum, firstly check
        # whether it remains ahead of all chis less than it for all times until
        # its upper bounds exceeds 1. Then, against all chis less than x,
        # verify the inequality from Lemma 4.6 at the final period where its upper
        # bound is less than 1. This verifies that the parameter space is
        # monotonically increasing to the left of the optimum.
        if chi <= first_chi_to_exceed_1:
            for x in [y for y in chi_list if y<chi]:
                for t in xrange(time_ui_exceeds_1_dict[first_chi_to_exceed_1],time_ui_exceeds_1_dict[chi]-1):
                    # Check lower bound on chi's fitness in previous iteration
                    # is greater than upper bound on x's fitness in current
                    # iteration.
                    if not (d[chi][0][t-1] > d[x][1][t]):
                        return False

            for x in [y for y in chi_list if y<chi]:
                if not ineq(chi,x,(relevant_coeffs_dict[chi][chi][0]-relevant_coeffs_dict[chi][x][1]),relevant_coeffs_dict[chi][chi][0],relevant_coeffs_dict[chi][x][0],relevant_coeffs_dict[chi][x][1],quantity_value_dict):
                    return False

            sys.stderr.write("Checked inequality for " + str(chi) + " against " + " ".join([str(x) for x in chi_list if x<chi]) + "\n")

        # For all chis `x' greater than or equal to the optimum, firstly check
        # whether it remains ahead of all chis greater than it for all times until
        # its upper bounds exceeds 1. Then, against all chis greater than x,
        # verify the inequality from Lemma 4.6 at the final period where its upper
        # bound is less than 1. This verifies that the parameter space is
        # monotonically decreasing to the right of the optimum.
        if chi >= first_chi_to_exceed_1:
            for x in [y for y in chi_list if y>chi]:
                for t in xrange(time_ui_exceeds_1_dict[first_chi_to_exceed_1],time_ui_exceeds_1_dict[chi]-1):
                    # Check lower bound on chi's fitness in previous iteration
                    # is greater than upper bound on x's fitness in current
                    # iteration.
                    if not (d[chi][0][t-1] > d[x][1][t]):
                        return False

            for x in [y for y in chi_list if y>chi]:
                if not ineq(chi,x,(relevant_coeffs_dict[chi][chi][0]-relevant_coeffs_dict[chi][x][1]),relevant_coeffs_dict[chi][chi][0],relevant_coeffs_dict[chi][x][0],relevant_coeffs_dict[chi][x][1],quantity_value_dict):
                    return False
            sys.stderr.write("Checked inequality for " + str(chi) + " against " + " ".join([str(x) for x in chi_list if x>chi]) + "\n")

    if verbose:
        for chi in chi_list:
            if chi<=first_chi_to_exceed_1:
                out_str = ""
                for x in chi_list:
                    if x < first_chi_to_exceed_1:
                        if x in quantity_value_dict[chi].keys():
                            out_str += "%0.1f & " %(quantity_value_dict[chi][x]*(100000))
                        else:
                            out_str += "-- & "
                out_str = out_str[:-2] + "\\\\"
                print out_str
            if chi>=first_chi_to_exceed_1:
                out_str = ""
                for x in chi_list:
                    if x > first_chi_to_exceed_1:
                        if x in quantity_value_dict[chi].keys():
                            out_str += "%0.1f & " %(quantity_value_dict[chi][x]*(100000))
                        else:
                            out_str += "-- & "
                out_str = out_str[:-2] + "\\\\"
                print out_str

    return True

def print_mono_best_chi_ranges(upper_time_limit, mono_best_chis,psi):
    # Note that this function crashes if there is not optimal value of chi for
    # any periods

    # Find the first chi which is at the optimum of a parameter space which has
    # been shown to be monotonically decreasing
    for i in xrange(1,upper_time_limit):
        if mono_best_chis[i] != 0:
            current_best = mono_best_chis[i]
            current_best_i = i
            break

    # Loop over all remaining periods, keeping track of which chi is optimal in
    # each one. Print the interval of cutoff times for which each chi is
    # optimal
    for i in xrange(current_best_i+1,upper_time_limit-1):
        if mono_best_chis[i] != current_best:
            if mono_best_chis[i] == 0:
                print current_best, "best chi for i in range", str(current_best_i/psi)+"n^2", str((i-1)/psi)+"n^2"
            current_best = mono_best_chis[i]
            current_best_i = i
    if mono_best_chis[i] != 0:
        print current_best, "best chi for i in range", str(current_best_i/psi)+"n^2", str(upper_time_limit/psi)+"n^2"


if __name__ == "__main__":
    psi = 1000000
    total_runtime = int(2.8 * psi) # Total number of iterations recurrences computed for
    
    coeff_dict = {}
    time_ui_exceeds_1_dict = {}
    
    # Defintion of the parameter spcae. Recall that around 1.6 is the optimal
    # value for chi for LeadingOnes.
    chi_list = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1.0,1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2.0,2.1,2.2,2.3,2.4,2.5,2.6,2.7,2.8,2.9,3.0]

    # Make this False to supress tables of inequality verification values and
    # coefficient intervals.
    verbose = True
    
    # Compute the coefficients for each value of chi.
    for chi in chi_list:
        sys.stderr.write("Computing coefficient bounds for chi = " + str(chi) + "\n")
        (l, u, time_ui_exceeds_1) = generate_li_ui(chi, psi, total_runtime)
        coeff_dict[chi] = (l,u)
        time_ui_exceeds_1_dict[chi] = time_ui_exceeds_1
        print "chi =", chi, "upper bound exceeds 1 at time", time_ui_exceeds_1_dict[chi]
    
    # Find the first point at which one of the upper bounds exceeds 1.
    time_first_ui_exceeds_1=total_runtime+1
    for chi in chi_list:
        if (time_ui_exceeds_1_dict[chi] < time_first_ui_exceeds_1) and (time_ui_exceeds_1_dict[chi]>0):
            time_first_ui_exceeds_1 = time_ui_exceeds_1_dict[chi]
            first_chi_to_exceed_1 = chi

    # Find and print ranges of cutoff times for which all intervals are
    # non-overlapping and monotonically decreasing either side of the optimum.
    mono_best_chis = verify_monotonicity(chi_list, coeff_dict, time_first_ui_exceeds_1)
    print_mono_best_chi_ranges(time_first_ui_exceeds_1, mono_best_chis, psi)

    # Verify whether the inequality holds which implies that the configuration
    # in front wins an evaluation in ParamRLS-F.
    if check_ineq(coeff_dict, chi_list, time_ui_exceeds_1_dict, first_chi_to_exceed_1, verbose):
        print "Used inequality to verify that the best chi remains ahead for cutoff times larger than (n^2/psi)*", time_first_ui_exceeds_1
    else:
        print "Unable to verify that the best chi remains ahead for cutoff times larger than (n^2/psi)", time_first_ui_exceeds_1

    # Print a file containing all intervals. Can print in LaTeX table format
    # using latex_output(coeff_dict)
    if verbose:
        txt_output(coeff_dict)
