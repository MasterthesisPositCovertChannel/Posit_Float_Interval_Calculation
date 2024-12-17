using SoftPosit
using CSV
using DataFrames

# ----------------------------
# Parameter Settings
# ----------------------------

# Set number_size to either 16 or 32 bits
const number_size = 16

# sign_mode determines whether positive or negative intervals should be calculated.
const sign_mode = :negative

# Exponent size for Posit arithmetic. Is set to es=2 as per the current Posit standard 2022.
const es = 2

# ----------------------------
# Helper Functions
# ----------------------------

"""
    negate_posit_bits(bits, nbits::Int) -> UInt

Applies two's complement negation to a given posit bit pattern:
- Flip all bits
- Add one
"""
function negate_posit_bits(bits, nbits::Int)
    mask = (UInt(1) << nbits) - 1
    flipped = (~bits) & mask
    negated = (flipped + 1) & mask
    return negated
end

"""
    bits_to_posit(bits::UInt, nbits::Int) -> Posit16 or Posit32

Interprets a given unsigned integer as a Posit of bit-size `nbits`.
"""
function bits_to_posit(bits::UInt, nbits::Int)
    if nbits == 16
        return Posit16(reinterpret(UInt16, UInt16(bits & 0xFFFF)))
    elseif nbits == 32
        return Posit32(reinterpret(UInt32, UInt32(bits & 0xFFFFFFFF)))
    else
        error("Unsupported number size for Posit. Choose 16 or 32.")
    end
end

"""
    posit_bits_to_string(bits, nbits::Int) -> String

Converts a posit bit pattern into a binary string.
"""
function posit_bits_to_string(bits, nbits::Int)
    if nbits == 16
        return bitstring(reinterpret(UInt16, bits))
    else
        return bitstring(reinterpret(UInt32, bits))
    end
end

"""
    ensure_float_order(f1, f2) -> (Float, Float)

Returns two given float values f1 and f2 in ascending order (f_lower, f_upper), ensuring that f_lower < f_upper.
"""
function ensure_float_order(f1, f2)
    return f1 < f2 ? (f1, f2) : (f2, f1)
end

"""
    ensure_posit_order(p1, p2) -> (Posit, Posit)

Returns two given posits p1 and p2 in ascending order.
"""
function ensure_posit_order(p1, p2)
    return Float64(p1) < Float64(p2) ? (p1, p2) : (p2, p1)
end

# ----------------------------
# Interval Computation Functions
# ----------------------------

"""
    compute_float_intervals(number_size::Int) -> Vector of NamedTuples

Calculates intervals for IEEE754 floats.
Each interval corresponds to a fixed exponent and all mantissa variations within that exponent.
Subnormal and special exponent values are excluded.

If sign_mode = :negative, produces negative intervals by setting the sign bit to 1.
"""
function calculate_float_intervals(number_size::Int)
    if number_size == 32
        exponent_bits = 8
        exponent_bias = 127
        mantissa_bits = 23
        FloatType = Float32
        UIntFType = UInt32
        total_bits = 32
    elseif number_size == 16
        exponent_bits = 5
        exponent_bias = 15
        mantissa_bits = 10
        FloatType = Float16
        UIntFType = UInt16
        total_bits = 16
    else
        error("Unsupported number size. Choose 16 or 32.")
    end

    float_intervals = []
    num_floats_in_interval = 2^mantissa_bits

    sign_bit_val = (sign_mode == :positive) ? 0 : 1

    # Iterate over normal exponent ranges, skipping subnormal and special exponents
    for E in 1:(2^exponent_bits - 2)
        E_actual = E - exponent_bias

        mantissa_lower = 0
        mantissa_upper = 2^mantissa_bits - 1

        bits_lower = (sign_bit_val << (total_bits - 1)) | (E << mantissa_bits) | mantissa_lower
        bits_upper = (sign_bit_val << (total_bits - 1)) | (E << mantissa_bits) | mantissa_upper

        f_lower = reinterpret(FloatType, UIntFType(bits_lower))
        f_upper = reinterpret(FloatType, UIntFType(bits_upper))

        (f_lower, f_upper) = ensure_float_order(f_lower, f_upper)

        bits_lower_str = bitstring(UIntFType(bits_lower))
        bits_upper_str = bitstring(UIntFType(bits_upper))

        push!(float_intervals, (
            E = E,
            E_actual = E_actual,
            bits_lower = bits_lower,
            bits_upper = bits_upper,
            f_lower = f_lower,
            f_upper = f_upper,
            float_lower_interval_cap = bits_lower_str,
            float_upper_interval_cap = bits_upper_str,
            num_floats_in_interval = num_floats_in_interval,
        ))
    end

    return float_intervals
end

"""
    construct_posit_bits(k, e, es, nbits) -> (bits, regime_length, exponent_bits_length, fraction_bits_length, regime_bits, exponent_bits_str, fraction_bits_str)

Calculates the "lowest" posit in a given interval specified by regime (k) and exponent (e).
Produces a bit pattern for the lower boundary of a posit interval (fraction bits = all zeros).
"""
function calculate_posit_bits(k::Int, e::Int, es::Int, nbits::Int)
    UIntType = nbits == 16 ? UInt16 : UInt32
    bits = zero(UIntType)
    position = nbits - 1

    # Always generating positive intervals first, will negate later if needed.
    # sign bit = 0
    position -= 1

    regime_bits = ""
    if k >= 0
        for _ in 1:(k+1)
            if position < 0
                break
            end
            bits |= (one(UIntType) << position)
            regime_bits *= "1"
            position -= 1
        end
        if position >= 0
            regime_bits *= "0"
            position -= 1
        end
    else
        for _ in 1:(-k)
            if position < 0
                break
            end
            # zeros already
            regime_bits *= "0"
            position -= 1
        end
        if position >= 0
            bits |= (one(UIntType) << position)
            regime_bits *= "1"
            position -= 1
        end
    end

    regime_length = length(regime_bits)
    remaining_bits = position + 1

    exponent_bits_length = min(es, remaining_bits)
    fraction_bits_length = remaining_bits - exponent_bits_length
    if fraction_bits_length < 0
        fraction_bits_length = 0
        exponent_bits_length = remaining_bits
    end

    exponent_bits_str = ""
    for i in (exponent_bits_length - 1):-1:0
        if position < 0
            break
        end
        bit = (e >> i) & 1
        bits |= (UInt(bit) << position)
        exponent_bits_str *= string(bit)
        position -= 1
    end

    fraction_bits_str = ""
    for _ in 1:fraction_bits_length
        if position < 0
            break
        end
        # zero bits by default
        fraction_bits_str *= "0"
        position -= 1
    end

    mask = (UInt(1) << nbits) - 1
    bits &= mask

    return bits, regime_length, exponent_bits_length, fraction_bits_length, regime_bits, exponent_bits_str, fraction_bits_str
end

"""
    construct_posit_bits_upper(k, e, es, nbits, fraction_bits_length) -> UInt

Calculates the "upper" posit in a given interval, where all fraction bits are set to one.
This represents the upper boundary of a posit interval.
"""
function calculate_posit_bits_upper(k::Int, e::Int, es::Int, nbits::Int, fraction_bits_length::Int)
    UIntType = nbits == 16 ? UInt16 : UInt32
    bits = zero(UIntType)
    position = nbits - 1

    # sign bit = 0 for positive
    position -= 1

    if k >= 0
        for _ in 1:(k+1)
            if position < 0
                break
            end
            bits |= (one(UIntType) << position)
            position -= 1
        end
        if position >= 0
            position -= 1
        end
    else
        for _ in 1:(-k)
            if position < 0
                break
            end
            # zero by default
            position -= 1
        end
        if position >= 0
            bits |= (one(UIntType) << position)
            position -= 1
        end
    end

    exponent_bits_length = min(es, position + 1)
    for i in (exponent_bits_length - 1):-1:0
        if position < 0
            break
        end
        bit = (e >> i) & 1
        bits |= (UInt(bit) << position)
        position -= 1
    end

    # fraction bits all ones
    for _ in 1:fraction_bits_length
        if position < 0
            break
        end
        bits |= (one(UIntType) << position)
        position -= 1
    end

    mask = (UInt(1) << nbits) - 1
    bits &= mask

    return bits
end

"""
    compute_posit_intervals(number_size::Int; es=2, nbits=number_size) -> Vector

Calculates posit intervals for given number_size.
Generates positive intervals first. If sign_mode = :negative, negates them.
"""
function calculate_posit_intervals(number_size::Int; es::Int = 2, nbits::Int = number_size)
    UIntType = nbits == 16 ? UInt16 : UInt32
    nbits = number_size
    posit_intervals = []

    max_k = nbits - 2
    min_k = -(nbits - 2)

    for k in min_k:max_k
        for e in 0:(2^es - 1)
            result = calculate_posit_bits(k, e, es, nbits)
            if result === nothing
                continue
            end
            bits_lower, regime_length, exponent_bits_length, fraction_bits_length, regime_bits, exponent_bits_str, fraction_bits_str = result
            bits_upper = calculate_posit_bits_upper(k, e, es, nbits, fraction_bits_length)

            p_lower = bits_to_posit(bits_lower, nbits)
            p_upper = bits_to_posit(bits_upper, nbits)
            (p_lower, p_upper) = ensure_posit_order(p_lower, p_upper)

            bits_lower_str = posit_bits_to_string(reinterpret(UIntType, p_lower), nbits)
            bits_upper_str = posit_bits_to_string(reinterpret(UIntType, p_upper), nbits)

            num_posits_in_interval = 2^fraction_bits_length

            push!(posit_intervals, (
                k = k,
                e = e,
                regime_length = regime_length,
                exponent_bits_length = exponent_bits_length,
                fraction_bits = fraction_bits_length,
                bits_lower = reinterpret(UIntType, p_lower),
                bits_upper = reinterpret(UIntType, p_upper),
                p_lower = p_lower,
                p_upper = p_upper,
                posit_lower_interval_cap = bits_lower_str,
                posit_upper_interval_cap = bits_upper_str,
                num_posits_in_interval = num_posits_in_interval,
            ))
        end
    end

    return posit_intervals
end

"""
    negate_posit_intervals(posit_intervals, nbits::Int) -> Vector

Calculates negative intervals, if sign_mode = :negative.
Takes positive intervals and negates them by applying two's complement negation.
"""
function negate_posit_intervals(posit_intervals, nbits::Int)
    UIntType = nbits == 16 ? UInt16 : UInt32
    neg_intervals = []
    for interval in posit_intervals
        bits_lower_pos = interval[:bits_lower]
        bits_upper_pos = interval[:bits_upper]

        bits_lower_neg = negate_posit_bits(bits_lower_pos, nbits)
        bits_upper_neg = negate_posit_bits(bits_upper_pos, nbits)

        p_lower_neg = bits_to_posit(bits_lower_neg, nbits)
        p_upper_neg = bits_to_posit(bits_upper_neg, nbits)
        (p_lower_neg, p_upper_neg) = ensure_posit_order(p_lower_neg, p_upper_neg)

        lower_str = posit_bits_to_string(reinterpret(UIntType, p_lower_neg), nbits)
        upper_str = posit_bits_to_string(reinterpret(UIntType, p_upper_neg), nbits)

        push!(neg_intervals, (
            k = interval[:k],
            e = interval[:e],
            regime_length = interval[:regime_length],
            exponent_bits_length = interval[:exponent_bits_length],
            fraction_bits = interval[:fraction_bits],
            bits_lower = reinterpret(UIntType, p_lower_neg),
            bits_upper = reinterpret(UIntType, p_upper_neg),
            p_lower = p_lower_neg,
            p_upper = p_upper_neg,
            posit_lower_interval_cap = lower_str,
            posit_upper_interval_cap = upper_str,
            num_posits_in_interval = interval[:num_posits_in_interval]
        ))
    end
    return neg_intervals
end

"""
    map_intervals(float_intervals, posit_intervals) -> Vector

Maps each float interval to a "best fitting" posit interval.
- If a posit interval covers the float interval, chooses the smallest range posit interval.
- If none cover it exactly, picks the closest by sum of absolute differences.
"""
function map_intervals(float_intervals, posit_intervals)
    mapping_results = []

    for float_interval in float_intervals
        f_lower = float_interval[:f_lower]
        f_upper = float_interval[:f_upper]

        candidate_posits = filter(posit_intervals) do posit_interval
            p_lower = Float64(posit_interval[:p_lower])
            p_upper = Float64(posit_interval[:p_upper])
            (p_lower <= f_lower && p_upper >= f_upper)
        end

        best_posit = nothing
        if isempty(candidate_posits)
            candidate_posits = sort(posit_intervals, by = x -> abs(Float64(x[:p_lower]) - f_lower) + abs(Float64(x[:p_upper]) - f_upper))
            best_posit = candidate_posits[1]
        else
            candidate_posits = sort(candidate_posits, by = x -> (Float64(x[:p_upper]) - Float64(x[:p_lower])))
            best_posit = candidate_posits[1]
        end

        result = merge(float_interval, best_posit)

        combined_result = NamedTuple(merge(result, (
            float_lower_interval_cap = float_interval[:float_lower_interval_cap],
            float_upper_interval_cap = float_interval[:float_upper_interval_cap],
            posit_lower_interval_cap = best_posit[:posit_lower_interval_cap],
            posit_upper_interval_cap = best_posit[:posit_upper_interval_cap]
        )))

        push!(mapping_results, combined_result)
    end

    return mapping_results
end

"""
    generate_csv_output(mapping_results, posit_intervals)

Writes the mapping results and posit intervals to CSV files.
"""
function generate_csv_output(mapping_results, posit_intervals)
    df_mapping = DataFrame(mapping_results)
    df_posits = DataFrame(posit_intervals)

    if sign_mode == :positive
        CSV.write("mapping_results.csv", df_mapping, missingstring="")
        CSV.write("posit_intervals.csv", df_posits, missingstring="")
    else
        CSV.write("mapping_results_negative.csv", df_mapping, missingstring="")
        CSV.write("posit_intervals_negative.csv", df_posits, missingstring="")
    end
end

# ----------------------------
# Main Execution
# ----------------------------

"""
    main()

Main function, calls all other functions in sequence.
"""
function main()
    println("Computing Float intervals...")
    float_intervals = calculate_float_intervals(number_size)
    println("Total Float intervals: $(length(float_intervals))")

    println("Computing Posit intervals...")
    posit_intervals = calculate_posit_intervals(number_size, es = es, nbits = number_size)
    println("Total Posit intervals: $(length(posit_intervals))")

    if sign_mode == :negative
        println("Negating Posit intervals for negative mode...")
        posit_intervals = negate_posit_intervals(posit_intervals, number_size)
        println("Total Negative Posit intervals: $(length(posit_intervals))")
    end

    println("Mapping intervals...")
    mapping_results = map_intervals(float_intervals, posit_intervals)
    println("Total mapping results: $(length(mapping_results))")

    println("Generating CSV outputs...")
    generate_csv_output(mapping_results, posit_intervals)
    if sign_mode == :positive
        println("CSV outputs saved: 'mapping_results.csv' and 'posit_intervals.csv'")
    else
        println("CSV outputs saved: 'mapping_results_negative.csv' and 'posit_intervals_negative.csv'")
    end
end

main()
