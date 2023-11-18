import numpy as np
from sklearn.linear_model import LinearRegression


# def linear_regression(X, y):
#     # Add a column of ones to X for the intercept term
#     X = np.column_stack((np.ones(len(X)), X))

#     # Calculate the coefficients using the normal equation
#     coefficients = np.linalg.inv(X.T.dot(X)).dot(X.T).dot(y)

#     return coefficients


def linearRegression(x_values, y_values):
    # Define the input and output variables
    x_values = np.array([10, 20, 30, 40, 50, 60, 70, 80, 90, 100])
    y_values = np.array([1, 2, 3, 4, 5, 6, 7, 8, 9, 10])

    # Reshape the input variable to a 2D array
    x_values = x_values.reshape(-1, 1)

    # Create a linear regression model and fit the data
    model = LinearRegression()
    model.fit(x_values, y_values)
    return model


def solveIterations(model, desired):
    return model.predict(desired)


linear_regression([1, 2], [3, 4])
